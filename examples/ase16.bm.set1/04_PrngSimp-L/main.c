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

inline int nC(int s2){ 
	int nC_return;
	do
	{
		nC_return = rand();
	}
	while(nC_return == s2 || nC_return == 0);
	return nC_return;
}

int seed = 1;

#ifdef SATABS
#define CAS(v,e,u,r) \
{ \
	__CPROVER_atomic_begin(); \
	if(v == e) \
	{ \
		v = u, r = 1; \
	} \
	else \
	{ \
		r = 0; \
	} \
	__CPROVER_atomic_end(); \
}
#else
#define CAS(v,e,u,r) \
{ __blockattribute__((atomic)) \
	if(v == e) \
	{ \
		v = u, r = 1; \
	} \
	else \
	{ \
		r = 0; \
	} \
}
#endif

#define min(x,y) ((y>=x)?(x):(y))

#define NUM 10

inline int PseudoRandomUsingAtomic_nex()
{
	int nex, nexts, casret, nex_return;
	while(1) {
		nex = seed;
		nexts = nC(nex);
		CAS(seed,nex,nexts,casret);

		if(casret == 1){
			nex_return = min(nexts,NUM);
			break;
		}
	}
	return nex_return;
}

void thr1(){
  assert(PseudoRandomUsingAtomic_nex() <= NUM);
}

#ifdef SATABS
int main()
{
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
#endif
