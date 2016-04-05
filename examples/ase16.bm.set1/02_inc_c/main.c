//http://www.ibm.com/developerworks/java/library/j-jtp04186/index.html
//Listing 2. A nonblocking counter using CAS

#ifdef SATABS
#define assume(e) __CPROVER_assume(e)
#define assert(e) __CPROVER_assert(e,"error")
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

volatile unsigned value;

unsigned thr1() {
	unsigned v,vn,casret;

	do {
		v = value;

		if(v == 0u-1) {
			return 0; 
		}

		vn = v + 1;

		CAS(value,v,vn,casret);
	}
	while (casret==0);
	assert(value > v); 

	return vn;
}

#ifdef SATABS
int main(){
	while(1) { __CPROVER_ASYNC_01: thr1(); }
}
#endif
