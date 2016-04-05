//#include <assert.h>

#ifdef SATABS
#define assert(e) __CPROVER_assert(e,"error")
#endif

int usecount;
int locked;
int flag1 = 0;
int flag2 = 0;
int release_thr1 = 0;

void thr2 () //dummy_open
{
  while(!release_thr1);

  usecount = usecount + 1;

  if (locked)
    return -1;
  locked = 1;
#ifdef SATABS
  __CPROVER_atomic_begin();
  flag1 = 1;
  __CPROVER_atomic_end();
#else
{ __blockattribute__((atomic))
  flag1 = 1;
}
#endif
  return;
}

inline void dummy_release ()
{
  usecount = usecount - 1;
  locked = 0;
  return;
}

inline void unregister_chrdev ()
{
  if (usecount != 0)
    {
    // this should fail
    ERROR: assert (0);
    }
  else
    return;
}

int thr1 ()
{
  int            rval;
  int count;

  usecount = 0;
  locked = 0;
  
  release_thr1 = 1; //__CPROVER_ASYNC_01: thr1 ();
  while(1)
  {
    if(flag1)
      break;
  }

  do
    {
      rval = thr1 ();
      if (rval == 0)
	{
	  count = 1;
	  dummy_release ();
	}
      else
	count = 0;
    }
  while	(count != 0);

  dummy_release ();

  unregister_chrdev ();

  return 0;
}

#ifdef SATABS
int main(){
	__CPROVER_ASYNC_01: thr1();
	while(1) { __CPROVER_ASYNC_02: thr2(); }
}
#endif

