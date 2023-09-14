#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdbool.h>

#define SIZE 512

#define MUX_RX_CH 0
#define CLIENT_CH 1

#define BUF_SIZE 2048
#define NUM_BUFFERS 512
#define SHARED_DMA_SIZE (BUF_SIZE * NUM_BUFFERS)

/* Buffer descriptor */
typedef struct buff_desc {
    uintptr_t encoded_addr; /* encoded dma addresses */
    unsigned int len; /* associated memory lengths */
    void *cookie; /* index into client side metadata */
} buff_desc_t;

/* Circular buffer containing descriptors */
typedef struct ring_buffer {
    uint32_t write_idx;
    uint32_t read_idx;
    uint32_t size;
    bool notify_writer;
    bool notify_reader;
    buff_desc_t buffers[SIZE];
} ring_buffer_t;

/* A ring handle for enqueing/dequeuing into  */
typedef struct ring_handle {
    ring_buffer_t *free_ring;
    ring_buffer_t *used_ring;
} ring_handle_t;

ring_buffer_t rx_free_mux;
ring_buffer_t rx_used_mux;

uintptr_t rx_free_cli;
uintptr_t rx_used_cli;

uintptr_t shared_dma_vaddr_mux;
uintptr_t shared_dma_vaddr_cli;
uintptr_t uart_base;

ring_handle_t rx_ring_mux;
ring_handle_t rx_ring_cli;



void ring_init(ring_handle_t *ring, ring_buffer_t *free, ring_buffer_t *used, int buffer_init, uint32_t free_size, uint32_t used_size)
/*@
requires ring_handle_free_ring(ring,_) &*& 
         ring_handle_used_ring(ring, _) &*&
         ring_buffer_write_idx(free,_) &*&
         ring_buffer_read_idx(free, _) &*&
         ring_buffer_size(free, _) &*&
         ring_buffer_notify_writer(free, _) &*&
         ring_buffer_notify_reader(free, _) &*&
         ring_buffer_write_idx(used, _) &*&
         ring_buffer_read_idx(used, _) &*&
         ring_buffer_size(used, _) &*&
         ring_buffer_notify_writer(used, _) &*&
         ring_buffer_notify_reader(used, _);
@*/
//@ensures true;
{
    ring->free_ring = free;
    ring->used_ring = used;

    if (buffer_init) {
        ring->free_ring->write_idx = 0;
        ring->free_ring->read_idx = 0;
        ring->free_ring->size = free_size;
        ring->free_ring->notify_writer = false;
        ring->free_ring->notify_reader = false;
        ring->used_ring->write_idx = 0;
        ring->used_ring->read_idx = 0;
        ring->used_ring->size = used_size;
        ring->used_ring->notify_writer =false;
        ring->used_ring->notify_reader = false;
    }
    /*@
    leak ring_handle_free_ring(ring,_) &*& 
         ring_handle_used_ring(ring, _) &*&
         ring_buffer_write_idx(free,_) &*&
         ring_buffer_read_idx(free, _) &*&
         ring_buffer_size(free, _) &*&
         ring_buffer_notify_writer(free, _) &*&
         ring_buffer_notify_reader(free, _) &*&
         ring_buffer_write_idx(used, _) &*&
         ring_buffer_read_idx(used, _) &*&
         ring_buffer_size(used, _) &*&
         ring_buffer_notify_writer(used, _) &*&
         ring_buffer_notify_reader(used, _);
    @*/
}

static inline bool ring_empty(ring_buffer_t *ring)
/*@
requires 
	ring_buffer_write_idx(ring, ?widx) &*& 
	ring_buffer_read_idx(ring, ?ridx) &*&
	widx >= ridx &*&  (widx >= 0) &*& ((widx - ridx) <= 4294967295) &*&
	ring_buffer_size(ring, ?size) &*& size > 0;
@*/
/*@
ensures true;
@*/
{
    return !((ring->write_idx - ring->read_idx) % ring->size);
    //@leak ring_buffer_read_idx(ring, _);
    //@leak ring_buffer_size(ring, _);
    //@leak ring_buffer_write_idx(ring, _);
}

static inline bool ring_full(ring_buffer_t *ring)
/*@
requires 
  ring_buffer_write_idx(ring, ?widx) &*&
  ring_buffer_read_idx(ring, ?ridx) &*&
  widx >= ridx &*& ((widx - ridx + 1) <= 4294967295) &*&
  ring_buffer_size(ring, ?size) &*& size > 0;
@*/
/*@
ensures true;
@*/
{
    assert((ring->write_idx - ring->read_idx) >= 0);
    return !((ring->write_idx - ring->read_idx + 1) % ring->size);
    //@leak ring_buffer_read_idx(ring, _);
    //@leak ring_buffer_size(ring, _);
    //@leak ring_buffer_write_idx(ring, _);
}

static inline uint32_t ring_size(ring_buffer_t *ring)
/*@
requires 
  ring_buffer_write_idx(ring, ?widx) &*&
  ring_buffer_read_idx(ring, ?ridx) &*&
  (0 <= (widx - ridx)) && ((widx - ridx) <= 4294967295);
@*/
/*@
ensures true;
@*/
{
    assert((ring->write_idx - ring->read_idx) >= 0);
    return (ring->write_idx - ring->read_idx);
    //@leak ring_buffer_write_idx(ring, _);
    //@leak ring_buffer_read_idx(ring, _);
}

static inline int enqueue(ring_buffer_t *ring, uintptr_t buffer, unsigned int len, void *cookie)
/*@
requires 
	buffer != 0 &*&
	ring_buffer_write_idx(ring, ?widx) &*&
	ring_buffer_read_idx(ring, ?ridx) &*&
	widx >= ridx &*&
	(widx - ridx + 1) <= 4294967295 &*&
	ring_buffer_size(ring, ?size) &*&
	size > 0 &*&
	ring_buffer_write_idx(ring, ?lwidx) &*&
	ridx <= lwidx &*&
	(lwidx - ridx + 1) <= 4294967295 &*&
	ring_buffer_size(ring, ?lsize) &*&
	lsize > 0
	;
@*/
/*@
ensures true;
@*/
{
    assert(buffer != 0);
    if (ring_full(ring)) {
        return -1;
        //@leak ring_buffer_write_idx(ring, widx);
        //@leak ring_buffer_size(ring, lsize);
    }

    ring->buffers[ring->write_idx % ring->size].encoded_addr = buffer;
    ring->buffers[ring->write_idx % ring->size].len = len;
    ring->buffers[ring->write_idx % ring->size].cookie = cookie;

    // THREAD_MEMORY_RELEASE();
    ring->write_idx++;

    return 0;
    //@leak ring_buffer_write_idx(ring, widx);
    //@leak ring_buffer_write_idx(ring, lwidx);
    //@leak ring_buffer_read_idx(ring, _);
    //@leak ring_buffer_size(ring, _);

}

static inline int dequeue(ring_buffer_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
{
    if (ring_empty(ring)) {
        return -1;
    }

    assert(ring->buffers[ring->read_idx % ring->size].encoded_addr != 0);

    *addr = ring->buffers[ring->read_idx % ring->size].encoded_addr;
    *len = ring->buffers[ring->read_idx % ring->size].len;
    *cookie = ring->buffers[ring->read_idx % ring->size].cookie;

    // THREAD_MEMORY_RELEASE();
    ring->read_idx++;

    return 0;
}

static inline int enqueue_free(ring_handle_t *ring, uintptr_t addr, unsigned int len, void *cookie)
{
    assert(addr);
    return enqueue(ring->free_ring, addr, len, cookie);
}

static inline int enqueue_used(ring_handle_t *ring, uintptr_t addr, unsigned int len, void *cookie)
{
    assert(addr);
    return enqueue(ring->used_ring, addr, len, cookie);
}

static inline int dequeue_free(ring_handle_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
{
    return dequeue(ring->free_ring, addr, len, cookie);
}

static inline int dequeue_used(ring_handle_t *ring, uintptr_t *addr, unsigned int *len, void **cookie)
{
    return dequeue(ring->used_ring, addr, len, cookie);
}

void process_rx_complete(void)
{
    uint64_t enqueued = 0;
    // We only want to copy buffers if all the dequeues and enqueues will be successful
    while (!ring_empty(rx_ring_mux.used_ring) &&
            !ring_empty(rx_ring_cli.free_ring) &&
            !ring_full(rx_ring_mux.free_ring) &&
            !ring_full(rx_ring_cli.used_ring)) {

        uintptr_t m_addr, c_addr = 0;
        unsigned int m_len, c_len = 0;
        void *cookie = NULL;
        void *cookie2 = NULL;
        int err;

        err = dequeue_used(&rx_ring_mux, &m_addr, &m_len, &cookie);
        assert(!err);
        // get a free one from clients queue.
        err = dequeue_free(&rx_ring_cli, &c_addr, &c_len, &cookie2);
        assert(!err);
        if (!c_addr ||
                c_addr < shared_dma_vaddr_cli ||
                c_addr >= shared_dma_vaddr_cli + SHARED_DMA_SIZE)
        {
            print("COPY|ERROR: Received an insane address: ");
            puthex64(c_addr);
            print(". Address should be between ");
            puthex64(shared_dma_vaddr_cli);
            print(" and ");
            puthex64(shared_dma_vaddr_cli + SHARED_DMA_SIZE);
            print("\n");
        }

        if (c_len < m_len) {
            print("COPY|ERROR: client buffer length is less than mux buffer length.\n");
            print("client length: ");
            puthex64(c_len);
            print(" mux length: ");
            puthex64(m_len);
            print("\n");
        }
        // copy the data over to the clients address space.
        memcpy((void *)c_addr, (void *)m_addr, m_len);

        /* Now that we've copied the data, enqueue the buffer to the client's used ring. */
        err = enqueue_used(&rx_ring_cli, c_addr, m_len, cookie2);
        assert(!err);
        /* enqueue the old buffer back to dev_rx_ring.free so the driver can use it again. */
        err = enqueue_free(&rx_ring_mux, m_addr, BUF_SIZE, cookie);
        assert(!err);

        enqueued += 1;
    }

    if (!ring_empty(rx_ring_mux.used_ring)) {
        // we want to be notified when this changes so we can continue
        // enqueuing packets to the client.
        rx_ring_cli.free_ring->notify_reader = true;
    } else {
        rx_ring_cli.free_ring->notify_reader = false;
    }

    if (rx_ring_cli.used_ring->notify_reader && enqueued) {
        sel4cp_notify(CLIENT_CH);
    }

    /* We want to inform the mux that more free buffers are available */
    if (enqueued && rx_ring_mux.free_ring->notify_reader) {
        sel4cp_notify_delayed(MUX_RX_CH);
    }
}


//void notified(int ch)
// requires (ch >= 0) && (ch <= 63);
// ensures true;
//{
    /* We have one job. */
//    process_rx_complete();
//}

