//original file: EBStack.java
//amino-cbbs\trunk\amino\java\src\main\java\org\amino\ds\lockfree
//push only

#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
#define assert(e) __CPROVER_assert(e,"error")
#endif

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

#define MEMSIZE (2*32+1) //0 for "NULL"
int memory[MEMSIZE];
#define INDIR(cell,idx) memory[cell+idx]

int next_alloc_idx = 1;

int top = 0;

#ifdef SATABS
#define index_malloc(curr_alloc_idx){\
	__CPROVER_atomic_begin();\
	if(next_alloc_idx+2-1 > MEMSIZE) curr_alloc_idx = 0;\
	else curr_alloc_idx = next_alloc_idx, next_alloc_idx += 2;\
	__CPROVER_atomic_end();\
}
#else
#define index_malloc(curr_alloc_idx){\
	{ __blockattribute__((atomic)) \
	if(next_alloc_idx+2-1 > MEMSIZE) curr_alloc_idx = 0;\
	else curr_alloc_idx = next_alloc_idx, next_alloc_idx += 2;\
	}\
}
#endif

#define isEmpty() (top == 0)

#define exit(r) assume(0);

inline void push(int d) {
	int oldTop, newTop,ret;
	index_malloc(newTop);
	if(newTop == 0)
		exit(-1);
	INDIR(newTop,0) = d;
	while (1) {
		oldTop = top;
		INDIR(newTop,1) = oldTop;
		CAS(top,oldTop,newTop,ret);
		if(ret)	return;
	}
}

int thr1(){
  while(1){push(10); assert(top != 0);}
}

#ifdef SATABS
int main()
{
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
#endif
