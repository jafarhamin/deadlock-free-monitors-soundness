#ifndef GHOSTR_RESOURCES_H
#define GHOST_RESOURCES_H

/*@
/*
Natural Numbers
*/

inductive nat = zero | succ(nat);

fixpoint int int_of_nat(nat n) {
    switch (n) {
        case zero: return 0;
        case succ(n0): return 1 + int_of_nat(n0);
    }
}

lemma void succ_pos(nat n)
    requires true;
    ensures int_of_nat(succ(n)) > 0;
{
  switch (n){
    case zero: ;
    case succ(n'): succ_pos(n');
  }
}

/*
Ghost Predicates
*/

predicate resource(int i);

predicate Resources(int i, nat Ct) =
  Resources(i,succ(Ct)) &*& resource(i);

/*
Ghost Resources Axioms
*/

lemma int create_g_id();
  requires true;
  ensures Resources(?i,zero) &*& result == i;

lemma nat resource_le_Resources(int i, nat n);
  requires Resources(i,n) &*& resource(i);
  ensures Resources(i,n) &*& resource(i) &*& exists(?n') &*& n == succ(n') &*& result == n';

/*
Ghost Resources Lemmas
*/

lemma void gain_g_resource(int i)
    requires Resources(i,?Ct);
    ensures Resources(i,succ(Ct)) &*& resource(i);
{
  open Resources(i,Ct);
}

lemma void lose_g_resource(int i)
    requires Resources(i,?Ct) &*& resource(i);
    ensures Resources(i,?Ct') &*& Ct == succ(Ct') &*& int_of_nat(Ct) > 0;
{
  nat n' = resource_le_Resources(i,Ct);
  switch (Ct){
    case zero: ;
    case succ(n): close Resources(i,n'); succ_pos(n');
  }
} 
@*/

#endif    