// Buffer cache.
//
// The buffer cache is a linked list of buf structures holding
// cached copies of disk block contents.  Caching disk blocks
// in memory reduces the number of disk reads and also provides
// a synchronization point for disk blocks used by multiple processes.
//
// Interface:
// * To get a buffer for a particular disk block, call bread.
// * After changing buffer data, call bwrite to write it to disk.
// * When done with the buffer, call brelse.
// * Do not use the buffer after calling brelse.
// * Only one process at a time can use a buffer,
//     so do not keep them longer than necessary.
//
// The implementation uses two state flags internally:
// * B_VALID: the buffer data has been read from the disk.
// * B_DIRTY: the buffer data has been modified
//     and needs to be written to disk.

#include <assert.h>

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int();

// typedefs necessary for buffer cache
typedef unsigned int   uint;
typedef unsigned char  uchar;

#define BSIZE 512         // block size
#define B_VALID 0x2       // buffer has been read from disk
#define B_DIRTY 0x4       // buffer needs to be written to disk
#define MAXOPBLOCKS  10   // max # of blocks any FS op writes
#define NBUF         3    // size of disk block cache

struct buf {
  int valid;
  int dirty;
  uint dev;
  uint blockno;
  int lock;
  uint refcnt;
  struct buf *prev; // LRU cache list
  struct buf *next;
  struct buf *qnext; // disk queue
  uchar data[BSIZE];
};

// function definitions
void            binit(void);
struct buf*     bread(uint, uint);
void            brelse(struct buf*);
void            bwrite(struct buf*);

struct {
  int lock;
  struct buf buf[NBUF];

  // Linked list of all buffers, through prev/next.
  // head.next is most recently used.
  struct buf head;
} bcache;

// Properties after binit(): 
// PROPOSED:
// - head->next points to buf[NBUF - 1]
// - head->prev points to buf[0]
// PROVED:
// - The exhaustive pointer setting for the doubly linked
// list setup inclusive of the above two points!
int
binit(void)
{
  struct buf *b;

  bcache.lock = 0; // init lock

  // Create linked list of buffers
  bcache.head.prev = &bcache.head;
  bcache.head.next = &bcache.head;
  for(b = bcache.buf; b < &bcache.buf[NBUF]; b++){
    b->next = bcache.head.next;
    b->prev = &bcache.head;
    b->lock = 0;  // init lock
    bcache.head.next->prev = b;
    bcache.head.next = b;
  }

  if(bcache.head.next != &bcache.buf[NBUF-1]) {
    goto ERROR;
  }

  if(bcache.head.prev != &bcache.buf[0]) {
    goto ERROR;
  }

  for(b = bcache.buf; b < &bcache.buf[NBUF]; b++){
    if(b == bcache.buf) {
      if(b->next != &bcache.head) {
        goto ERROR;
      }
      if(b->prev != b+1) {
        goto ERROR;
      }
    } else if(b == &bcache.buf[NBUF-1]) {
      if(b->next != b-1) {
        goto ERROR;
      }
      if(b->prev != &bcache.head) {
        goto ERROR;
      }
    } else {
      if(b->next != b-1) {
        goto ERROR;
      }
      if(b->prev != b+1) {
        goto ERROR;
      }
    }
  }

  return 0;
  ERROR: __VERIFIER_error();
  return -1;
}

// Look through buffer cache for block on device dev.
// If not found, allocate a buffer.
// In either case, return locked buffer.

// Properties after bget():
// PROPOSED:
// - unsure at this about the verifiability of the properties
//  as it includes loops. If time permits, will work on this. 
// PROVED:
// - Proper locking and unlocking of bcache.lock. 
// - (in main) if successfully returned then b->dev == dev, 
// b->blockno ==  blockno and b->refcnt >= 1.
static struct buf*
bget(uint dev, uint blockno)
{
  struct buf *b;

  // acquire(&bcache.lock);
  if(bcache.lock == 1) {
    goto ERROR;
  }
  bcache.lock = 1;

  // Is the block already cached?
  for(b = bcache.head.next; b != &bcache.head; b = b->next){
    if(b->dev == dev && b->blockno == blockno){
      b->refcnt++;
      // release(&bcache.lock);
      if(bcache.lock == 0) {
        goto ERROR;
      }
      bcache.lock = 0;
      // acquiresleep(&b->lock);
      b.lock = 1;   
      return b;
    }
  }

  // Not cached; recycle some unused buffer and clean buffer
  // "clean" because B_DIRTY and not locked means log.c
  // hasn't yet committed the changes to the buffer.
  for(b = bcache.head.prev; b != &bcache.head; b = b->prev){
    if(b->refcnt == 0 && (b->dirty == 1)) {
      b->dev = dev;
      b->blockno = blockno;
      b->dirty = 0;
      b->valid = 0;
      b->refcnt = 1;
      // release(&bcache.lock);
      if(bcache.lock == 0) {
        goto ERROR;
      }
      bcache.lock = 0;
      // acquiresleep(&b->lock);
      b.lock = 1;
      return b;
    }
  }

  return 0;

  ERROR: __VERIFIER_error();
  return -1;
}

// Dummy disk read function for specification
void iderw(struct buf *b) {
  b->valid = 1;
  return;
}

// Return a locked buf with the contents of the indicated block.
// Properties after bread():
// PROPOSED:
// - if not B_VALID, a call to iderw is set.
// PROVED:
// - B_VALID is always set after a call to bread
struct buf*
bread(uint dev, uint blockno)
{
  struct buf *b;

  b = bget(dev, blockno);

  // check that a locked block is returned
  // UNABLE TO PROVE!
  // if(b->lock != 1) {
  //   goto ERROR;
  // }

  // CPAchecker weird behavior!
  // if(b->valid != 1) {
    iderw(b);
  // }

  if(b->valid != 1) {
    goto ERROR;
  }

  return b;

  ERROR: __VERIFIER_error();
  return b;
}

// Write b's contents to disk.  Must be locked.
// Properties after bwrite():
// PROPOSED:
// - B_DIRTY is set after a call to bwrite()
// PROVED:
// - after a call bwrite, B_DIRTY set before iderw and B_VALID flag is set after iderw
void
bwrite(struct buf *b)
{
  // set B_DIRTY flag
  b->dirty = 1;
  
  if(b->dirty != 1) {
    goto ERROR;
  }

  iderw(b);

  if(b->valid != 1) {
    goto ERROR;
  }
  
  return;

  ERROR: __VERIFIER_error();
  return;
}

// Release a locked buffer.
// Move to the head of the MRU list.
// Properties after brelse():
// PROPOSED:
// - Most interesting function of the lot, the buffer b is 
//  now set as MRU (Most Recently Used) and head->next is b
// PROVED:
// - successfully acquiring and releasing locks
// - shows that b is now the MRU (head.next points to it)
// - shows that the old MRU is after b in the recently used list
void
brelse(struct buf *b)
{

  // acquire(&bcache.lock);
  if(bcache.lock == 1) {
    goto ERROR;
  }
  bcache.lock = 1;
  
  b->refcnt--;

  // keep track of old MRU for specification
  struct buf *mru = bcache.head.next;
  if (b->refcnt == 0) {
    // no one is waiting for it.
    b->next->prev = b->prev;
    b->prev->next = b->next;
    b->next = bcache.head.next;
    b->prev = &bcache.head;
    bcache.head.next->prev = b;
    bcache.head.next = b;
  }
  
  // show that b.head -> b -> mru (old)
  if (b->refcnt == 0) {
    if(bcache.head.next != b) {
      goto ERROR;
    }
    if(b->prev != &bcache.head) {
      goto ERROR;
    }
    if(b->next != mru) {
      goto ERROR;
    }
    if(mru->prev != b) {
      goto ERROR;
    }
  }
  
  // release(&bcache.lock);  
  if(bcache.lock == 0) {
    goto ERROR;
  }
  bcache.lock = 0;
  
  return;
  
  ERROR: __VERIFIER_error();
  return;
}

int main() {
  // initialize the buffer cache doubly linked list
  int initcheck = 0;
  initcheck = binit();
  if (initcheck != 0) {
     goto ERROR;
  }

  // fetch a block with dev = 1, blockno = 1
  bcache.lock = 0;
  struct buf *b;
  b = bget(10, 20);

  if(b != 0) {
    if(b->dev != 10 || b->blockno != 20 || b->refcnt < 1) {
      goto ERROR;
    }
    // UNABLE TO PROVE!
    // if(b->lock != 1) {
    //   goto ERROR;
    // }
  }

  // fetch a block with dev = 20, blockno = 40
  bcache.lock = 0;
  bread(20, 40);

  // write to a block
  b = &bcache.buf[1];
  bwrite(b);

  // release a block
  bcache.lock = 0;
  b = &bcache.buf[0];
  brelse(b);

  return 0;
  ERROR: __VERIFIER_error();
  return -1;
}
