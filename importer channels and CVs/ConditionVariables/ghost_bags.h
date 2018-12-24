/*
  Ghost Importers
*/

#include "levels_with_importers.h"

#ifndef GHOST_BAGS_H
#define GHOST_BAGS_H

/*@
predicate gbag(void* id, list<void*> O);

lemma void* new_gbag();
  requires true;
  ensures Mr(result) == nil;

lemma void gbag_trandit(void* gbag);
  requires obs(?O,?I);
  ensures obs(O,cons(gbag,I)) &*& trandit(gbag);

lemma void gbag_add(void* gbag, list<void*> O');
  requires obs(?O,?I) &*& trandit(gbag) &*& forall(map(level_of, O'),(mem')(Mr(gbag))) == true;
  ensures obs(minus(O,O'),I) &*& gbag(gbag,O');

lemma void gbag_remove(void* gbag, list<void*> O');
  requires obs(?O,?I) &*& gbag(gbag,O');
  ensures obs(append(O,O'),remove(gbag,I));
@*/

#endif