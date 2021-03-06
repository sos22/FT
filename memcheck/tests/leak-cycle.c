#include <stdlib.h>
#include "../memcheck.h"

struct n {
	struct n *l;
	struct n *r;
};

struct n *mk(struct n *l, struct n *r)
{
	struct n *n = malloc(sizeof(*n));
	n->l = l;
	n->r = r;

	return n;
}

static struct n *mkcycle()
{
	register struct n *a, *b, *c;

	a = mk(0,0);
	b = mk(a,0);
	c = mk(b,0);
	a->l = c;

	return a;
}

int main()
{

	struct n *volatile c1, *volatile c2;

	/* two simple cycles */
	c1 = mkcycle();
	c2 = mkcycle();

	c1 = c2 = 0;

	//VALGRIND_DO_LEAK_CHECK;

	/* one cycle linked to another */
	c1 = mkcycle();
	c2 = mkcycle();

	/* This is to make sure we end up merging cliques; see
	   mc_leakcheck.c */
	if (c1 < c2)
		c2->r = c1;
	else
		c1->r = c2;

	c1 = c2 = 0;

	//VALGRIND_DO_LEAK_CHECK;

	/* two linked cycles */
	c1 = mkcycle();
	c2 = mkcycle();

	c1->r = c2;
	c2->r = c1;

	c1 = c2 = 0;

	VALGRIND_DO_LEAK_CHECK;

	return 0;
}
