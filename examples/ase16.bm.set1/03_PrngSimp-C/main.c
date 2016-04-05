//http://www.ibm.com/developerworks/java/library/j-jtp11234/
//Listing 5. Implementing a thread-safe PRNG with synchronization and atomic variables

#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
#define assert(e) __CPROVER_assert(e,"error")
#endif

#ifdef SATABS
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

#define min(x,y) ((y>=x)?(x):(y))

int m = 0;
inline int calculateNext(int s2){ 
	int cnex;
	do cnex = rand();
	while(cnex == s2 || cnex == 0);
	return cnex;
}

int seed = 1; 

#define NUM 10

inline int PseudoRandomUsingAtomic_nextInt() {
	int read, nexts, nextInt_return;

	assert(seed != 0);

	acquire(m);
	read = seed;
	nexts = calculateNext(read);
	seed = nexts;
	release(m);
	nextInt_return = min(nexts,NUM);
	return nextInt_return;
}

void thr1(){
  PseudoRandomUsingAtomic_nextInt();
}

#ifdef SATABS
int main()
{
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
#endif
