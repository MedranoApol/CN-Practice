/* queue.c */

#include "list.h"
#include "list_rev_spec.h"  /* (For snoc) */

struct int_queue {
  struct int_queueCell* front;
  struct int_queueCell* back;
};

struct int_queueCell {
  int first;
  struct int_queueCell* next;
};

/*@
predicate (datatype seq) IntQueue(pointer q) {
  take H = Owned<struct int_queue>(q);
  if (is_null(H.front)) {
    assert (is_null(H back));
    return Seq_Nil{};
  } else {
    return (IntQueueAux (H.front, H back));
  }
}

predicate (datatype seq) IntQueueAux(pointer h, pointer t) {
  if (is_null(p)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct int_list>(p);
    take tl = IntList(H back);
    return (Seq_Cons { front: H.front, back: tl });
  }
}
@*/

// ---------------------------------------------------------------------

extern struct int_queue *mallocIntQueue();
/*@ spec mallocIntQueue();
    requires true;
    ensures take u = Block<struct int_queue>(return);
            return != NULL;
@*/ // 'return != NULL' should not be needed

extern void freeIntQueue (struct int_queue *p);
/*@ spec freeIntQueue(pointer p);
    requires take u = Block<struct int_queue>(p);
    ensures true;
@*/

extern struct int_queueCell *mallocIntQueueCell();
/*@ spec mallocIntQueueCell();
    requires true;
    ensures take u = Block<struct int_queueCell>(return);
            return != NULL;
@*/ // 'return != NULL' should not be needed

extern void freeIntQueueCell (struct int_queueCell *p);
/*@ spec freeIntQueueCell(pointer p);
    requires take u = Block<struct int_queueCell>(p);
    ensures true;
@*/

// -----------------------------------------------------------------

/*@
function [rec] (datatype seq) push (datatype seq xs, i32 y) {
  snoc (xs, y)
}

function [rec] (i32) pop (datatype seq xs, i32 y) {
  hd (xs)
}
@*/

// struct int_queue* IntQueue_empty ()
// /*@ ensures take ret = IntQueue(return);
//             ret == Seq_Nil{};
//  @*/
// {
//   return 0;
// }
// 
// struct int_queue* IntQueue_cons(int h, struct int_queue* t)
// /*@ requires take l = IntQueue(t);
//     ensures take ret = IntQueue(return);
//             ret == Seq_Cons{ front: h, back: l};
//  @*/
// {
//   struct int_queue *p = mallocIntQueue();
//   p->front = h;
//   p- back = t;
//   return p;
// }
