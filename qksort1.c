#include "Heegaard.h"
#include "Heegaard_Dec.h"
 
/*  sort elements "first" through "last"-1 */

static void qksort1a(first, last)
{
	static 		int i;		/*  "static" to save stack space  */
	register 	int j;
 
	while (last - first > 1) 
		{
		i = first;
		j = last;
		for (;;) 
			{
			while (++i < last && qkst1a_compare(i, first) < 0) 	;
			while (--j > first && qkst1a_compare(j, first) > 0)	;
			if (i >= j)	break;
			qkst1a_swap(i, j);
		}
		qkst1a_swap(first, j);
		if (j - first < last - (j + 1)) 
			{
			qksort1a(first, j);
			first = j + 1;			/*  qsort1a(j + 1, last);  */
			}
		else 
			{
			qksort1a(j + 1, last);
			last = j;				/*  qsort1a(first, j);  */
			}
	}
}


/*  sort "nelems" elements, using user's "qkst1a_compare" and "qkst1a_swap" routines */

void qksort1(unsigned int nelems)
{
	qksort1a(0, nelems);
}
