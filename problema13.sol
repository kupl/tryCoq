Proof
assert forall (nat1:nat), half (plus (nat1) (nat1)) = nat1
induction nat1
reflexivity
simpl in goal
assert forall (nat1:nat), half (SUCC (plus (nat1) (SUCC (nat1)))) = SUCC (nat1)
induction nat1
reflexivity
simpl in goal
rewrite <- IH1 in goal at 2
assert forall (nat1:nat), plus (nat1) (SUCC (SUCC (nat1))) = SUCC (plus (nat1) (SUCC (nat1)))
induction nat1
simpl in goal
reflexivity
simpl in goal
assert forall (nat1:nat) (nat2:nat), plus (nat1) (SUCC (nat2)) = SUCC (plus (nat1) (nat2))
induction nat1
simpl in goal
reflexivity
simpl in goal
rewrite IH1 in goal at 0
reflexivity
rewrite lemma3 in goal at 0
rewrite lemma3 in goal at 0
simpl in goal
rewrite lemma3 in goal at 0
reflexivity
rewrite lemma4 in goal at 1
reflexivity
rewrite lemma5 in goal at 0
reflexivity
Qed