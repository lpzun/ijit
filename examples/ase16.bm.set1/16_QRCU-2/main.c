// #include <assert.h> //CP: gcc preprocessor inlines the assert
// #include <pthread.h>

#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
#define atomic(e,f) __CPROVER_atomic_begin(),e,f,__CPROVER_atomic_end()
#define acquire(m) atomic(assume(!m),m = !m)
#define release(m) atomic(assume(m),m = !m)
#endif

#define LOCKED 1

#define mtx_lock(m) acquire(m);assert(m==LOCKED); //acquire lock and ensure no other thread unlocked it
#define mtx_unlock(m) release(m)

volatile _Bool MTX = !LOCKED;

int idx; // bit idx = 0; controls which of the two elements ctr1 or ctr2 will be used by readers
int ctr1, ctr2; // byte ctr[2];
int readerprogress1, readerprogress2; // byte readerprogress[N_QRCU_READERS];
int mutex; // bit mutex = 0; updates are done in critical section, only one writer at a time
int NONDET;

void* qrcu_reader1() {
  int myidx;
  
  /* rcu_read_lock */
  while (1) {
    myidx = idx;
    if (NONDET) {
      { //__blockattribute__((atomic))
	mtx_lock(MTX);
	assume(myidx <= 0);
	assume(ctr1>0);
	ctr1++;
	mtx_unlock(MTX);
      }
      break;
    } else {
      if (NONDET) {
	{ //__blockattribute__((atomic))
	  mtx_lock(MTX);
	  assume(myidx > 0);
	  assume(ctr2>0);
	  ctr2++;
	  mtx_unlock(MTX);
	}
	break;
      } else {}
    }
  }
  /* This is a simpler code for rcu_read_lock, but the frontend generates too many transitions
  while (1) {
    myidx = idx;
    if (myidx <= 0 && ctr1>0) {
      ctr1++; break;
    } else {
      if (myidx > 0 && ctr2>0) {
	ctr2++; break;
      } else {}
    }
    } */

  readerprogress1 = 1; /*** readerprogress[me] = 1; ***/
  readerprogress1 = 2; /*** readerprogress[me] = 2 ***/

  /* rcu_read_unlock */
  { //__blockattribute__((atomic))
      mtx_lock(MTX);
      if (myidx <= 0) { ctr1--; } // use ctr1
      else { ctr2--; } // use ctr2
      mtx_unlock(MTX);
  }
}

/* sums the pair of counters forcing weak memory ordering */
#define sum_unordered \
  if (NONDET) {       \
    sum = ctr1;       \
    sum = sum + ctr2; \
  } else {            \
    sum = ctr2;       \
    sum = sum + ctr1; \
  }

void* qrcu_updater() {
  int i;
  int readerstart1;
  int readerstart2;
  int sum;

  glb_init(idx==0);
  glb_init(ctr1==1);
  glb_init(ctr2==0);
  glb_init(readerprogress1==0);
  glb_init(readerprogress2==0);
  glb_init(mutex==0);  

  /* Snapshot reader state. */
  {// __blockattribute__((atomic))
      mtx_lock(MTX);
      readerstart1 = readerprogress1;
      readerstart2 = readerprogress2;
      mtx_unlock(MTX);
  }

  sum_unordered;
  if (sum <= 1) { sum_unordered; }
  if (sum > 1) {
    acquire(mutex);
    if (idx <= 0) { ctr2++; idx = 1; ctr1--; }
    else { ctr1++; idx = 0; ctr2--; }
    if (idx <= 0) { while (ctr2 > 0); }
    else { while (ctr1 > 0); }
    release(mutex);
  }

  /* Verify reader progress. */
  { //__blockattribute__((atomic))
      mtx_lock(MTX);
      if (NONDET) {
	assume(readerstart1 == 1);
	assume(readerprogress1 == 1);
	assert(0);
      } else {
	if (NONDET) {
	  assume(readerstart2 == 1);
	  assume(readerprogress2 == 1);
	  assert(0);
	} else { }
      }
      mtx_unlock(MTX);
  }
  /* Frontend generates too many transitions:
  { __blockattribute__((atomic))
      sum = 0;
      if (readerstart1 == 1 && readerprogress1 == 1)
	sum++;
      if (readerstart2 == 1 && readerprogress2 == 1)
	sum++;
      assert(sum == 0);
      } */

}

void* qrcu_reader2() {
  int myidx;
  
  /* rcu_read_lock */
  while (1) {
    myidx = idx;
    if (NONDET) {
      { //__blockattribute__((atomic))
	mtx_lock(MTX);
	assume(myidx <= 0);
	assume(ctr1>0);
	ctr1++;
	mtx_unlock(MTX);
      }
      break;
    } else {
      if (NONDET) {
	{ //__blockattribute__((atomic))
	  mtx_lock(MTX);
	  assume(myidx > 0);
	  assume(ctr2>0);
	  ctr2++;
	  mtx_unlock(MTX);
	}
	break;
      } else {}
    }
  }

  readerprogress2 = 1; /*** readerprogress[me] = 1; ***/
  readerprogress2 = 2; /*** readerprogress[me] = 2 ***/

  /* rcu_read_unlock */
  { //__blockattribute__((atomic))
    mtx_lock(MTX);
      if (myidx <= 0) { ctr1--; } // use ctr1
      else { ctr2--; } // use ctr2
      mtx_unlock(MTX);

  }
}

#define acquire_thread_id(tid, l) \
  { mtx_lock(MTX); \
    assume(l==0); \
    l = tid; \
  mtx_lock(MTX); \
  }

#ifdef SATABS
int main() {
  /* pthread_t t1, t2, t3; */

  /* pthread_create(&t1, NULL, qrcu_reader1, NULL); */
  /* pthread_create(&t2, NULL, qrcu_reader2, NULL); */
  /* pthread_create(&t3, NULL, qrcu_writer, NULL); */

  while(1) { 
  __CPROVER_ASYNC_01: qrcu_reader1(); 
  __CPROVER_ASYNC_01: qrcu_reader2();
  __CPROVER_ASYNC_01: qrcu_writer();
  }

} 
#endif
