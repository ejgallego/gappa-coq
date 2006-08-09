Require Import Gappa_common.

Section Gappa_proxy.

Theorem fix_of_flt_bnd :
 forall x : R, forall xi : FF, forall m : Z, forall n : positive,
 FLT x n -> ABS x xi ->
 true = true ->
 FIX x m.
Admitted.

Theorem flt_of_fix_bnd :
 forall x : R, forall xi : FF, forall m : Z, forall n : positive,
 FIX x m -> ABS x xi ->
 true = true ->
 FLT x n.
Admitted.

End Gappa_proxy.
