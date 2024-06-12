/* queue.c */

struct int_list {
  int head;
  struct int_list* tail;
};

struct int_queue {
  struct int_list* front;
  struct int_list* back;
};

extern struct int_list *mallocIntList();
/*@ spec mallocIntList();
    requires true;
    ensures take u = Block<struct int_list>(return);
            return != NULL;
@*/ // 'return != NULL' should not be needed

extern void freeIntList (struct int_list *p);
/*@ spec freeIntList(pointer p);
    requires take u = Block<struct int_list>(p);
    ensures true;
@*/

/*@
datatype seq {
  Seq_Nil {},
  Seq_Cons {i32 head, datatype seq tail}
}

predicate (datatype seq) IntList(pointer p) {
  if (is_null(p)) {
    return Seq_Nil{};
  } else {
    take H = Owned<struct int_list>(p);
    take tl = IntList(H.tail);
    return (Seq_Cons { head: H.head, tail: tl });
  }
}
@*/

/*@
predicate ({datatype seq front, datatype seq back}) IntQueue(pointer q) {
  take Q = Owned<struct int_queue>(q);
  let q_Front = Q.front;
  let q_Back = Q.back;
  take f = IntList(q_Front);
  take b = IntList(q_Back);

  let ret = (f == Seq_Nil{} && b == Seq_Nil{}) ? {front: Seq_Nil{}, back: Seq_Nil{}} :
       ((f == Seq_Nil{} && b != Seq_Nil{}) ? {front: Seq_Nil{}, back: b} :
       ((f != Seq_Nil{} && b == Seq_Nil{}) ? {front: f, back: Seq_Nil{}} :
                                            {front: f, back: b}));
  return ret;
}
@*/