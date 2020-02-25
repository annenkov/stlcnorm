(** * Notation for reasoning using several transitive steps *)

(** This implementation uses several notations defined for different number of transitive steps. While it is not general and not very elegant, it currently works better than the one defined using Coq's recursive notations *)

(** This way of writing proofs is inspired by Lean and also available in Agda. The current implementations is not as general as Lean/Agda and allows for chaining only equality steps. Ideally, it should support any transitive relation and support any number of transitivity steps. *)

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 'end'" :=
  (@eq_trans _ a0 b0 b1 t0 t1) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 'end'" :=
  (@eq_trans _ a0 b0 b2 t0 (@eq_trans _ b0 b1 b2 t1 t2)) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 'end'" :=
  (@eq_trans _ a0 b0 _ t0 (@eq_trans _ b0 b1 _ t1 (@eq_trans _ b1 b2 b3 t2 t3))) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 ; '_' = b4 'by' t4 'end'" :=
  (@eq_trans _ a0 b0 b4 t0
             (@eq_trans _ b0 b1 b4 t1
                        (@eq_trans _ b1 b2 b4 t2 (@eq_trans _ b2 b3 b4 t3 t4)))) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 ; '_' = b4 'by' t4 ; '_' = b5 'by' t5 'end'" :=
  (@eq_trans _ a0 b0 _ t0
             (@eq_trans _ b0 b1 _ t1
                        (@eq_trans _ b1 b2 _ t2 (@eq_trans _ b2 b3 _ t3 (@eq_trans _ b3 b4 b5 t4 t5))))) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 ; '_' = b4 'by' t4 ; '_' = b5 'by' t5 ; '_' = b6 'by' t6 'end'" :=
  (@eq_trans _ a0 b0 _ t0
             (@eq_trans _ b0 b1 _ t1
                        (@eq_trans _ b1 b2 _ t2
                                   (@eq_trans _ b2 b3 _ t3
                                              (@eq_trans _ b3 b4 _ t4 (@eq_trans _ b4 b5 b6 t5 t6)))))) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 ; '_' = b4 'by' t4 ; '_' = b5 'by' t5 ; '_' = b6 'by' t6 ; '_' = b7 'by' t7 'end'" :=
  (@eq_trans _ a0 b0 _ t0
             (@eq_trans _ b0 b1 _ t1
                        (@eq_trans _ b1 b2 _ t2
                                   (@eq_trans _ b2 b3 _ t3
                                              (@eq_trans _ b3 b4 _ t4
                                                         (@eq_trans _ b4 b5 _ t5 (@eq_trans _ b5 b6 b7 t6 t7))))))) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 ; '_' = b4 'by' t4 ; '_' = b5 'by' t5 ; '_' = b6 'by' t6 ; '_' = b7 'by' t7 ; '_' = b8 'by' t8 'end'" :=
  (@eq_trans _ a0 b0 _ t0
             (@eq_trans _ b0 b1 _ t1
                        (@eq_trans _ b1 b2 _ t2
                                   (@eq_trans _ b2 b3 _ t3
                                              (@eq_trans _ b3 b4 _ t4
                                                         (@eq_trans _ b4 b5 _ t5
                                                                    (@eq_trans _ b5 b6 _ t6 (@eq_trans _ b6 b7 b8 t7 t8)))))))) (at level 70, a0 at next level, only parsing) : calc_scope.

Notation "'calc' a0 = b0 'by' t0 ; '_' = b1 'by' t1 ; '_' = b2 'by' t2 ; '_' = b3 'by' t3 ; '_' = b4 'by' t4 ; '_' = b5 'by' t5 ; '_' = b6 'by' t6 ; '_' = b7 'by' t7 ; '_' = b8 'by' t8 ; '_' = b9 'by' t9 'end'" :=
  (@eq_trans _ a0 b0 _ t0
             (@eq_trans _ b0 b1 _ t1
                        (@eq_trans _ b1 b2 _ t2
                                   (@eq_trans _ b2 b3 _ t3
                                              (@eq_trans _ b3 b4 _ t4
                                                         (@eq_trans _ b4 b5 _ t5
                                                                    (@eq_trans _ b5 b6 b7 t6
                                                                               (@eq_trans _ b6 b7 _ t7 (@eq_trans _ b7 b8 b9 t8 t9))))))))) (at level 70, a0 at next level, only parsing) : calc_scope.
