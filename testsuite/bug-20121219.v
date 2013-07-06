Require Import Reals.
Require Import Fcore.
Require Import Gappa_tactic.

Coercion F2R : float >-> R.

Lemma glo :
  forall x_0 y : float radix2,
  (Rabs (x_0 * y) <= 22471164185778948846616314884862809170224712236778832159178760144716584475687620391588559665300942002640014234983924169707348721101802077811605928829934265547220986678108185659537777450155761764931635369010625721104768835292807860184239138817603404645418813835573287279993405742309964538104419541203028017152)%R ->
  (Rabs (round radix2 (FLT_exp (-1074) 26) ZnearestE x_0 *
         round radix2 (FLT_exp (-1074) 26) ZnearestE y - x_0 * y) <= powerRZ 2 2000)%R ->
  (1 <= Rabs x_0 <= 334846439745708537796382827831250565800439003657979252326171996365734703476542538279124493379904955664873335286735358382870982901778848138624518049209330462622955242963257218294408581408199098183686068192282702343236935664606211486223923248314908216080349889927704442739388432239144512088662677127168)%R ->
  (1 <= Rabs y <= 334846439745708537796382827831250565800439003657979252326171996365734703476542538279124493379904955664873335286735358382870982901778848138624518049209330462622955242963257218294408581408199098183686068192282702343236935664606211486223923248314908216080349889927704442739388432239144512088662677127168)%R ->
  (Rabs
    (round radix2 (FLT_exp (-1074) 53) ZnearestE
      (round radix2 (FLT_exp (-1074) 26) ZnearestE x_0 *
       round radix2 (FLT_exp (-1074) 26) ZnearestE y)) <=
  9007199254740991 * powerRZ 2 971)%R.
Proof.
intros.
gappa.
Qed.