#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
#define assert(e) __CPROVER_assert(e,"error")

#define acquire(m) \
{ \
  __CPROVER_atomic_begin(); \
	assume(m==0); \
	m = 1; \
	__CPROVER_atomic_end(); \
}
#define release(m) \
{ \
  __CPROVER_atomic_begin(); \
	assume(m==1); \
	m = 0; \
	__CPROVER_atomic_end(); \
}
#endif

#define WORKPERTHREAD 2
#define THREADSMAX 3
volatile int max = 0x80000000, m = 0;

int storage[WORKPERTHREAD*THREADSMAX];

inline void findMax(int offset)
{
	int i;
	int e;

	for(i = offset; i < offset+WORKPERTHREAD; i++) {
		e = storage[i];
		
		acquire(m);
		{
			if(e > max) {
				max = e;
			}
		}
		release(m);
		assert(e <= max);
	}
}

void thr1() {
	int offset;

#ifdef SATABS
	assume(offset % WORKPERTHREAD == 0 && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
#else
	assume(offset < WORKPERTHREAD && offset >= 0 && offset < WORKPERTHREAD*THREADSMAX);
#endif

	findMax(offset);
}

#ifdef SATABS
int main(){
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
#endif
