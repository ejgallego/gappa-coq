Require Import IA_real.
Require Import IA_comput.

Section IA_manip.

Theorem add_decomposition :
 forall a b c d : R,
 forall ai bi ci di zi : FF,
 IintF ai a -> IintF bi b -> IintF ci c -> IintF di d ->
 IintF zi ((a - c) + (b - d))%R -> IintF zi ((a + b) - (c + d))%R.
intros a b c d ai bi ci di zi Ha Hb Hc Hd Hz.
replace ((a + b) - (c + d))%R with ((a - c) + (b - d))%R.
exact Hz.
ring.
Qed.

Theorem sub_decomposition :
 forall a b c d : R,
 forall ai bi ci di zi : FF,
 IintF ai a -> IintF bi b -> IintF ci c -> IintF di d ->
 IintF zi ((a - c) - (b - d))%R -> IintF zi ((a - b) - (c - d))%R.
intros a b c d ai bi ci di zi Ha Hb Hc Hd Hz.
replace ((a - b) - (c - d))%R with ((a - c) - (b - d))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_simple :
 forall a b c d : R,
 forall ai bi ci di zi : FF,
 IintF ai a -> IintF bi b -> IintF ci c -> IintF di d ->
 IintF zi (a * (b - d) + d * (a - c))%R -> IintF zi (a * b - c * d)%R.
intros a b c d ai bi ci di zi Ha Hb Hc Hd Hz.
replace (a * b - c * d)%R with (a * (b - d) + d * (a - c))%R.
exact Hz.
ring.
Qed.

Theorem mul_decomposition_full_left :
 forall a b c d : R,
 forall ai bi ci di zi : FF,
 IintF ai a -> IintF bi b -> IintF ci c -> IintF di d ->
 IintF zi (a * (b - d) + b * (a - c) - (a - c) * (b - d))%R -> IintF zi (a * b - c * d)%R.
intros a b c d ai bi ci di zi Ha Hb Hc Hd Hz.
replace (a * b - c * d)%R with (a * (b - d) + b * (a - c) - (a - c) * (b - d))%R.
exact Hz.
ring.
Qed.


End IA_manip.
