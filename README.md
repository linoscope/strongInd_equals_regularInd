# strongInd_equals_regularInd
完全帰納法が（普通の）数学的帰納法と同値であることの証明

```
∀P. P(0) ∧ (∀k.(∀m.m <= k -> P(m)) ->  P(k+1)) -> ∀n.P(n)
⇔
∀P. P(0) ∧ (∀k.P(k) ->  P(k+1)) -> ∀n.P(n)
```