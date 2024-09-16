```agda
{-# OPTIONS --without-K --rewriting #-}
module part3 where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import part1
open import part2
```

# Polynomial Universes

## Univalence

For any polynomial `𝔲 = (A , B)` and elements `a,b : A`, we may define a function that takes a proof of `a ≡ b` to an equivalence `B a ≃ B b`.

```agda
idToEquiv : ∀ {ℓ κ} (p : Poly ℓ κ) (a b : fst p)
            → a ≡ b → Σ (snd p a → snd p b) isEquiv
idToEquiv p a b e = 
      transp (snd p) e
    , Iso→isEquiv (transp (snd p) (sym e) , (syml e , symr e))
```

We say that a polynomial `𝔲` is *univalent* if for all `a,b : A`, this function is an equivalence.

```agda
isUnivalent : ∀ {ℓ κ} → Poly ℓ κ → Type (ℓ ⊔ κ)
isUnivalent (A , B) = 
    (a b : A) → isEquiv (idToEquiv (A , B) a b)
```

We call this property of polynomials univalence by analogy with the usual univalence axiom of HoTT. Indeed, the univalence axiom simply states that the polynomial functor `(Type , λ X → X)` is itself univalent.

```agda
postulate
    ua : ∀ {ℓ} → isUnivalent (Type ℓ , λ X → X)
```

A key property of polynomial universes – qua polynomial functors – is that every polynomial universe `𝔲` is a *subterminal object* in $\mathbf{Poly^{Cart}}$, i.e. for any other polynomial `p`, the type of Cartesian lenses `p ⇆ 𝔲` is a proposition, i.e. any two Cartesian lenses with codomain `𝔲` are equal.

```agda
isSubterminal : ∀ {ℓ κ} (u : Poly ℓ κ) → Setω
isSubterminal u = ∀ {ℓ' κ'} (p : Poly ℓ' κ')
                  → (f g : p ⇆ u)
                  → isCartesian p u f
                  → isCartesian p u g
                  → EqLens p u f g
```

To show this, we first prove the following *transport lemma*, which says that transporting along an identity `a ≡ b` induced by an equivalence `f : B a ≃ B b` in a univalent polynomial `p = (A , B)` is equivalent to applying `f`.

```agda
transpLemma : ∀ {ℓ κ} {𝔲 : Poly ℓ κ}
              → (univ : isUnivalent 𝔲) 
              → {a b : fst 𝔲} (f : snd 𝔲 a → snd 𝔲 b)
              → (ef : isEquiv f) (x : snd 𝔲 a)
              → transp (snd 𝔲) (inv (univ a b) (f , ef)) x ≡ f x
transpLemma {𝔲 = 𝔲} univ {a = a} {b = b} f ef x = 
    coAp (ap fst (snd (snd (univ a b)) ((f , ef)))) x
```

The result then follows:

```agda
univ→Subterminal : ∀ {ℓ κ} (u : Poly ℓ κ)
                   → isUnivalent u
                   → isSubterminal u
univ→Subterminal u univ p f g cf cg a = 
    ( inv univfg (fg⁻¹ , efg⁻¹) 
    , (λ b → sym ((snd g a (transp (snd u)  (inv univfg (fg⁻¹ , efg⁻¹)) b)) 
                  ≡〈 (ap (snd g a) (transpLemma univ fg⁻¹ efg⁻¹ b)) 〉 
                  ((snd g a (fg⁻¹ b)) 
                  ≡〈 snd (snd (cg a)) (snd f a b) 〉 
                  ((snd f a b) □)))))
    where univfg : isEquiv (idToEquiv u (fst f a) (fst g a))
          univfg = univ (fst f a) (fst g a)
          fg⁻¹ : snd u (fst f a) → snd u (fst g a)
          fg⁻¹ x = inv (cg a) (snd f a x)
          efg⁻¹ : isEquiv fg⁻¹
          efg⁻¹ = compIsEquiv (inv (cg a)) (snd f a) 
                              (invIsEquiv (cg a)) (cf a)
```

We shall refer to polynomial functors with this property of being subterminal objects in $\mathbf{Poly^{Cart}}$ as *polynomial universes.* As we shall see, such polynomial universes have many desirable properties as models of type theory.

If we think of a polynomial `p` as representing a family of types, then what this tells us is that if `𝔲` is a polynomial universe, there is essentially at most one way for `𝔲` to contain the types represented by `p`, where Containment is here understood as existence of a Cartesian lens `p ⇆ 𝔲`. In this case, we say that `𝔲` *classifies* the types represented by `p`.

As a direct consequence of this fact, it follows that every diagram consisting of parallel Cartesian lenses into a polynomial universe automatically commutes, and moreover, every higher diagram that can be formed between the cells exhibiting such commutation must also commute, etc.

Hence the fact that `𝔲` must satisfy the laws of a monad if there are Cartesian lenses `η : 𝕪 ⇆ 𝔲` and  `μ : 𝔲 ◃ 𝔲 ⇆ 𝔲` follows immediately from the above theorem and the closure of Cartesian lenses under composition:

```agda
univ◃unitl : ∀ {ℓ κ} (𝔲 : Poly ℓ κ) → isUnivalent 𝔲
             → (η : 𝕪 ⇆ 𝔲) (μ : (𝔲 ◃ 𝔲) ⇆ 𝔲)
             → isCartesian 𝕪 𝔲 η → isCartesian (𝔲 ◃ 𝔲) 𝔲 μ
             → EqLens (𝕪 ◃ 𝔲) 𝔲 
                      (◃unitl 𝔲)
                      (comp (𝕪 ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲
                            (◃Lens 𝕪 𝔲 𝔲 𝔲 η (id 𝔲)) μ)
univ◃unitl 𝔲 univ η μ cη cμ =
    univ→Subterminal 
        𝔲 univ (𝕪 ◃ 𝔲) (◃unitl 𝔲)
        (comp (𝕪 ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲 
              (◃Lens 𝕪 𝔲 𝔲 𝔲 η (id 𝔲)) μ) 
        (◃unitlCart 𝔲) 
        (compCartesian (𝕪 ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲
                       (◃Lens 𝕪 𝔲 𝔲 𝔲 η (id 𝔲)) μ 
                       (◃LensCart 𝕪 𝔲 𝔲 𝔲 η (id 𝔲) 
                                  cη (idCart 𝔲)) cμ)

univ◃unitr : ∀ {ℓ κ} (𝔲 : Poly ℓ κ) → isUnivalent 𝔲
             → (η : 𝕪 ⇆ 𝔲) (μ : (𝔲 ◃ 𝔲) ⇆ 𝔲)
             → isCartesian 𝕪 𝔲 η → isCartesian (𝔲 ◃ 𝔲) 𝔲 μ
             → EqLens (𝔲 ◃ 𝕪) 𝔲
                      (◃unitr 𝔲)
                      (comp (𝔲 ◃ 𝕪) (𝔲 ◃ 𝔲) 𝔲
                            (◃Lens 𝔲 𝔲 𝕪 𝔲 (id 𝔲) η) μ)
univ◃unitr 𝔲 univ η μ cη cμ =
    univ→Subterminal 
        𝔲 univ (𝔲 ◃ 𝕪) (◃unitr 𝔲) 
        (comp (𝔲 ◃ 𝕪) (𝔲 ◃ 𝔲) 𝔲 
              (◃Lens 𝔲 𝔲 𝕪 𝔲 (id 𝔲) η) μ) 
        (◃unitrCart 𝔲) 
        (compCartesian (𝔲 ◃ 𝕪) (𝔲 ◃ 𝔲) 𝔲 
                       (◃Lens 𝔲 𝔲 𝕪 𝔲 (id 𝔲) η) μ 
                       (◃LensCart 𝔲 𝔲 𝕪 𝔲 (id 𝔲) η 
                                  (idCart 𝔲) cη) cμ)


univ◃assoc : ∀ {ℓ κ} (𝔲 : Poly ℓ κ) → isUnivalent 𝔲
             → (η : 𝕪 ⇆ 𝔲) (μ : (𝔲 ◃ 𝔲) ⇆ 𝔲)
             → isCartesian 𝕪 𝔲 η → isCartesian (𝔲 ◃ 𝔲) 𝔲 μ
             → EqLens ((𝔲 ◃ 𝔲) ◃ 𝔲) 𝔲
                      (comp ((𝔲 ◃ 𝔲) ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲
                            (◃Lens (𝔲 ◃ 𝔲) 𝔲 𝔲 𝔲 μ (id 𝔲)) μ)
                      (comp ((𝔲 ◃ 𝔲) ◃ 𝔲) (𝔲 ◃ (𝔲 ◃ 𝔲)) 𝔲
                            (◃assoc 𝔲 𝔲 𝔲)
                            (comp (𝔲 ◃ (𝔲 ◃ 𝔲)) (𝔲 ◃ 𝔲) 𝔲
                                  (◃Lens 𝔲 𝔲 (𝔲 ◃ 𝔲) 𝔲 
                                         (id 𝔲) μ) μ))
univ◃assoc 𝔲 univ η μ cη cμ =
    univ→Subterminal 
        𝔲 univ ((𝔲 ◃ 𝔲) ◃ 𝔲) 
        (comp ((𝔲 ◃ 𝔲) ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲 
              (◃Lens (𝔲 ◃ 𝔲) 𝔲 𝔲 𝔲 μ (id 𝔲)) μ) 
        (comp ((𝔲 ◃ 𝔲) ◃ 𝔲) (𝔲 ◃ (𝔲 ◃ 𝔲)) 𝔲 
              (◃assoc 𝔲 𝔲 𝔲) 
              (comp (𝔲 ◃ (𝔲 ◃ 𝔲)) (𝔲 ◃ 𝔲) 𝔲 
                    (◃Lens 𝔲 𝔲 (𝔲 ◃ 𝔲) 𝔲 (id 𝔲) μ) μ)) 
        (compCartesian ((𝔲 ◃ 𝔲) ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲 
                       (◃Lens (𝔲 ◃ 𝔲) 𝔲 𝔲 𝔲 μ (id 𝔲)) μ 
                       (◃LensCart (𝔲 ◃ 𝔲) 𝔲 𝔲 𝔲 μ (id 𝔲) 
                                  cμ (idCart 𝔲)) cμ)
        (compCartesian ((𝔲 ◃ 𝔲) ◃ 𝔲) (𝔲 ◃ (𝔲 ◃ 𝔲)) 𝔲 
                       (◃assoc 𝔲 𝔲 𝔲) 
                       (comp (𝔲 ◃ (𝔲 ◃ 𝔲)) (𝔲 ◃ 𝔲) 𝔲 
                             (◃Lens 𝔲 𝔲 (𝔲 ◃ 𝔲) 𝔲 
                                    (id 𝔲) μ) μ) 
                       (◃assocCart 𝔲 𝔲 𝔲)
                       (compCartesian 
                          (𝔲 ◃ (𝔲 ◃ 𝔲)) (𝔲 ◃ 𝔲) 𝔲 
                          (◃Lens 𝔲 𝔲 (𝔲 ◃ 𝔲) 𝔲 (id 𝔲) μ) μ 
                          (◃LensCart 𝔲 𝔲 (𝔲 ◃ 𝔲) 𝔲 (id 𝔲) μ 
                                     (idCart 𝔲) cμ) cμ))
```

And more generally, all the higher coherences of an $\infty$-monad should follow from the contractibility of the types of Cartesian lenses `p ⇆ 𝔲` that can be formed using `μ` and `η`. 

### Rezk Completion of Polynomial Functors

We have so far seen that polynomial universes are quite special objects in the theory of polynomial functors in HoTT, but what good would such special objects do us if they turned out to be exceedingly rare or difficult to construct? In fact, we can show that for *any* polynomial functor, there exists a corresponding polynomial universe, using a familiar construct from the theory of categories in HoTT – the *Rezk Completion.* We will show that this construction allows us to quotient any polynomial functor to a corresponding polynomial universe.

By our assumption of the univalence axiom, every polynomial functor `p` is classified by *some* univalent polynomial:

```agda
classifier : ∀ {ℓ κ} (p : Poly ℓ κ) → p ⇆ (Type κ , λ X → X)
classifier (A , B) = (B , λ a b → b)

classifierCart : ∀ {ℓ κ} (p : Poly ℓ κ) 
                 → isCartesian p (Type κ , λ X → X)
                               (classifier p)
classifierCart p a = idIsEquiv
```

We then obtain the Rezk completion of `p` as the image factorization in $\mathbf{Poly^{Cart}}$ of this classifying lens:

```agda
Rezk : ∀ {ℓ κ} (p : Poly ℓ κ) → Poly (lsuc κ) κ
Rezk (A , B) = (Im B) , (λ (X , _) → X)

→Rezk : ∀ {ℓ κ} (p : Poly ℓ κ) → p ⇆ (Rezk p)
→Rezk {κ = κ} p = 
    factorcart1 p (Type κ , λ X → X) 
                  (classifier p) 
                  (classifierCart p)

Rezk→ : ∀ {ℓ κ} (p : Poly ℓ κ) → (Rezk p) ⇆ (Type κ , λ X → X)
Rezk→ {κ = κ} p =
    factorcart2 p (Type κ , λ X → X) 
                  (classifier p) 
                  (classifierCart p)
```

Because the map `Rezk→` defined above is a Cartesian embedding, and the polynomial `(Type κ , λ X → X)` is univalent, it follows that `Rezk p` is a polynomial universe:

```agda
RezkSubterminal : ∀ {ℓ κ} (p : Poly ℓ κ) → isSubterminal (Rezk p)
RezkSubterminal {κ = κ} p q (f , f♯) (g , g♯) cf cg x =
    ( pairEq (inv (ua (fst (f x)) (fst (g x))) 
                  ( (λ y → inv (cg x) (f♯ x y)) 
                  , compIsEquiv (inv (cg x)) 
                                (f♯ x) 
                                (invIsEquiv (cg x)) 
                                (cf x))) ∥-∥IsProp 
    , λ y → f♯ x y 
            ≡〈 sym (g♯ x (transp (λ X → X) 
                                  (inv (ua (fst (f x)) (fst (g x))) 
                                       ((λ z → inv (cg x) (f♯ x z)) , (compIsEquiv (inv (cg x)) (f♯ x) 
                                                    (invIsEquiv (cg x)) 
                                                    (cf x)))) y)
                    ≡〈 (ap (g♯ x) 
                          (transpLemma ua 
                             (λ z → inv (cg x) (f♯ x z)) 
                             (compIsEquiv (inv (cg x)) (f♯ x) 
                                          (invIsEquiv (cg x)) (cf x)) 
                             y)) 〉 
                    snd (snd (cg x)) (f♯ x y)) 〉 
            ap (g♯ x) (sym (lemma1 ∥-∥IsProp y)) )
    where lemma1 : {a b : fst (Rezk p)}
                   → {e : fst a ≡ fst b} 
                   → (e' : transp (λ c → ∥ (Fibre (snd p) c) ∥) 
                                  e (snd a) 
                           ≡ (snd b))
                   → (z : fst a)
                   → transp (snd (Rezk p)) (pairEq e e') z
                     ≡ transp (λ X → X) e z
          lemma1 {e = refl} refl z = refl
```