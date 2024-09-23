```agda
{-# OPTIONS --without-K --rewriting --lossy-unification #-}
module part4v2 where

open import part1v2
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import part2v2
open import appendixA
open import part3v2
```

# Polynomial Universes

## Univalence

For any polynomial `𝔲 = (𝓤 , El)`, we say that `𝔲` is *univalent* if `𝔲` is a *subterminal object* in $\mathbf{Poly^{Cart}}$, i.e. for any other polynomial `p`, the type of Cartesian lenses `p ⇆ 𝔲` is a proposition, i.e. any two Cartesian lenses with codomain `𝔲` are equal.

```agda
isUnivalent : ∀ {ℓ κ} → Poly ℓ κ → Setω
isUnivalent u = 
    ∀ {ℓ' κ'} {p : Poly ℓ' κ'}
      → {f g : p ⇆ u}
      → isCartesian u f
      → isCartesian u g
      → EqLens u f g
    
```

We call this property of polynomials univalence in analogy with the usual univalence axiom of HoTT. Indeed, the univalence axiom can be equivalently stated as the fact that the polynomial functor `(Type , λ X → X)` is itself univalent.

```agda
postulate
    ua : ∀ {ℓ} → isUnivalent (Type ℓ , λ X → X)
```

We shall refer to univalent polynomial functors as *polynomial universes.* f we think of a polynomial `p` as representing a family of types, then what this tells us is that if `𝔲` is a polynomial universe, there is essentially at most one way for `𝔲` to contain the types represented by `p`, where Containment is here understood as existence of a Cartesian lens `p ⇆ 𝔲`. In this case, we say that `𝔲` *classifies* the types represented by `p`.

As a direct consequence of this fact, it follows that every diagram consisting of parallel Cartesian lenses into a polynomial universe automatically commutes, and moreover, every higher diagram that can be formed between the cells exhibiting such commutation must also commute, etc.

Hence the fact that `𝔲` must satisfy the laws of a monad if there are Cartesian lenses `η : 𝕪 ⇆ 𝔲` and  `μ : 𝔲 ◃ 𝔲 ⇆ 𝔲` follows immediately from the above theorem and the closure of Cartesian lenses under composition:

```agda
module UnivMonad {ℓ κ} (𝔲 : Poly ℓ κ) (univ : isUnivalent 𝔲)
                 (η : 𝕪 ⇆ 𝔲) (μ : (𝔲 ◃ 𝔲) ⇆ 𝔲)
                 (cη : isCartesian 𝔲 η) (cμ : isCartesian 𝔲 μ) where

    univ◃unitl : EqLens 𝔲 (◃unitl 𝔲) (comp 𝔲 (η ◃◃[ 𝔲 ] (id 𝔲)) μ)
    univ◃unitl = univ (◃unitlCart 𝔲) 
                      (compCartesian 𝔲 (◃◃Cart 𝔲 𝔲 cη (idCart 𝔲)) cμ)

    univ◃unitr : EqLens 𝔲 (◃unitr 𝔲) (comp 𝔲 ((id 𝔲) ◃◃[ 𝔲 ] η) μ)
    univ◃unitr = univ (◃unitrCart 𝔲) 
                      (compCartesian 𝔲 (◃◃Cart 𝔲 𝔲 (idCart 𝔲) cη) cμ)


    univ◃assoc : EqLens 𝔲 (comp 𝔲 (μ ◃◃[ 𝔲 ] (id 𝔲)) μ)
                          (comp 𝔲 (◃assoc 𝔲 𝔲 𝔲)
                                  (comp 𝔲 ((id 𝔲) ◃◃[ 𝔲 ] μ) μ))
    univ◃assoc = univ (compCartesian 𝔲 (◃◃Cart 𝔲 𝔲 cμ (idCart 𝔲)) cμ)
                      (compCartesian 𝔲 (◃assocCart 𝔲 𝔲 𝔲)
                                       (compCartesian 𝔲 (◃◃Cart 𝔲 𝔲 (idCart 𝔲) cμ) cμ))

open UnivMonad public
```

And more generally, all the higher coherences of an $\infty$-monad would follow -- if we bothered to write them out -- from the contractibility of the types of Cartesian lenses `p ⇆ 𝔲` that can be formed using `μ` and `η`.

### Examples of Polynomial Universes

We have so far seen that polynomial universes are quite special objects in the theory of polynomial functors in HoTT, but what good would such special objects do us if they turned out to be exceedingly rare or difficult to construct? 

In fact, polynomial universes are surprisingly plentiful in univalent type theory. We have already seen how the univalence axiom implies that `(Type , λ X → X)` is a polynomial universe. From this single example, a plethora of others can be seen to follow, many of which encompass familiar constructs from programming and mathematics.

In a sense, the polynomial `(Type , λ X → X)` is *universal* among polynomials in $\mathbf{Poly}^{\mathbf{Cart}}$ in that, for any polynomial `p`, there is a (necessarily unique, by univalence) Cartesian morphism `p ⇆ (Type , λ X → X)`. Or rather, there would be, were it not for the size issues preventing `(Type , λ X → X)` from being a single object. Instead, it can more accurately be said that the family of polynomials `(Type ℓ , λ X → X)` for all `ℓ : Level` is universal among polynomials in $\mathbf{Poly}^{\mathbf{Cart}}$ – this can be shown straightforwardly as follows:

```agda
module PolyCartUniv {ℓ κ} (p : Poly ℓ κ) where

    classifier : p ⇆ (Type κ , λ X → X)
    classifier = (snd p , λ _ b → b)

    classifierCart : isCartesian (Type κ , λ X → X) classifier
    classifierCart _ = idIsEquiv
```

In other words, every polynomial functor `p` is classified by some polynomial universe. Moreover, if the classifying morphism `p ⇆ (Type κ , λ X → X)` is a Vertical embedding (i.e. a monomorphism in $\mathbf{Poly}^{\mathbf{Cart}}$), then `p` itself is also a polynomial universe – for any pair of Cartesian morphisms `f g : q ⇆ p`, since `(Type κ , λ X → X)` is univalent, we have `classifier ∘ f ≡ classifier ∘ g`, but then since `classifier` is assumed to be a monomorphism, this implies that `f ≡ g`.

```agda
    polyCartUniv : isVerticalEmbedding (Type κ , λ X → X) classifier → isUnivalent p
    polyCartUniv veclassifier cf cg = 
        VertEmbedding→PolyCartMono
            (Type κ , λ X → X) 
            classifierCart 
            veclassifier
            cf cg 
            (ua (compCartesian _ cf classifierCart) 
                (compCartesian _ cg classifierCart))

open PolyCartUniv public
```

It follows that, for any type family `P : Type → Type`, we can create a polynomial *sub-universe* of `(Type , λ X → X)` by restricting to those types `X` for which there *merely* exists an inhabitant of `P X`.

```agda
module SubUniv {ℓ κ} (P : Type ℓ → Type κ) where

    subUniv : Poly (lsuc ℓ) ℓ
    subUniv = (Σ (Type ℓ) (λ X → ∥ P X ∥) , λ (X , _) → X)

    subUnivClassifierIsVerticalEmbedding :
        isVerticalEmbedding (Type ℓ , λ X → X) (classifier subUniv)
    subUnivClassifierIsVerticalEmbedding = 
        Iso→isEquiv ( (λ e → pairEq e ∥-∥IsProp) 
                    , ( (λ e → (pairEq (ap (fst (classifier subUniv)) e) ∥-∥IsProp) 
                               ≡〈 ap (λ e' → pairEq (ap (fst (classifier subUniv)) e) e') ∥-∥≡Contr 〉 
                               ( _ 
                               ≡〈 (pairEqη e) 〉 
                               (e □))) 
                      , (λ e → pairEqβ1 e ∥-∥IsProp) ) )
    
    subUnivIsUniv : isUnivalent subUniv
    subUnivIsUniv = polyCartUniv subUniv subUnivClassifierIsVerticalEmbedding

open SubUniv public
```

As a first example of a polynomial universe other than `(Type , λ X → X)`, then, we may consider the polynomial universe of *propositions* `ℙ`:

```agda
module PropUniv where

    ℙ : Poly (lsuc lzero) lzero
    ℙ = subUniv isProp
```

If we write out explicitly the polynomial endofunctor defined by `ℙ` we see that it has the following form: $$
y \mapsto \sum_{\phi : \mathbf{Prop}} y^\phi
$$ This endofunctor (in fact it is a monad) is well-known in type theory by another name – the *partiality* monad. Specifically, this is the monad `M` whose kleisli morphisms `A → M B` correspond to *partial functions* from `A` to `B`, that associate to each element `a : A`, a proposition `def f a` indicating whether or not the value of `f` is defined at `a`, and a function `val : def f a → B` that takes a proof that `f` is defined at `a` to its value at `a`.

If we return to the original example of the polynomial universe `(Type , λ X → X)` we see that the associated polynomial endofunctor (which, by the above argument, is also a monad) has a similar form. $$
y \mapsto \sum_{X : \mathbf{Type}} y^X
$$ In this case, we can think of this as a "proof relevant" partiality monad `M`, such that a function `f : A → M B` associates to each element `a : A` a *type* `Def f a` of proofs that `f` is defined at `a`, and a function `val : Def f a → B`.[^1]

[^1]: the conception of the monad determined by `(Type , λ X → X)` as a "proof relevant" partiality monad was communicated to the first author during private conversations with Jonathan Sterling.

More generally, we can say that, for any polynomial universe closed under dependent pair types, the associated monad will be a kind of (potentially proof-relevant) partiality monad, where the structure of the polynomial universe serves to dictate which types can count as *evidence* for whether or not a value is defined.

#### Rezk Completion

In fact, we can show that for *any* polynomial functor, there exists a corresponding polynomial universe, using a familiar construct from the theory of categories in HoTT – the *Rezk Completion.* We will show that this construction allows us to quotient any polynomial functor to a corresponding polynomial universe.

We obtain the Rezk completion of `p` as the image factorization in $\mathbf{Poly^{Cart}}$ of the classifying morphism of `p`:

```agda
module RezkCompletion {ℓ κ} (p : Poly ℓ κ) where

    Rezk : Poly (lsuc κ) κ
    Rezk = cartIm (Type κ , λ X → X) (classifier p) (classifierCart p)

    →Rezk : p ⇆ Rezk
    →Rezk = factorcart1 (Type κ , λ X → X) (classifier p) (classifierCart p)

    Rezk→ : Rezk ⇆ (Type κ , λ X → X)
    Rezk→ = factorcart2 (Type κ , λ X → X) (classifier p) (classifierCart p)
```

The polynomial `Rezk` defined above can be seen to have the same form as a subuniverse of `(Type , λ X → X)`; hence it is a polynomial universe, as desired.

```agda
    RezkUniv : isUnivalent Rezk
    RezkUniv = subUnivIsUniv (λ X → Σ (fst p) (λ a → (snd p a) ≡ X))

open RezkCompletion public
```

As an example of how the Rezk completion allows us to "upgrade" a polynomial functor (a polynomial monad, even) into a polynomial universe, consider the following definition of the finite ordinals as a family of types indexed by the type `Nat` of natural numbers:

```agda
module FinUniv where
    open import Agda.Builtin.Nat
```

We first define the standard ordering on natural numbers:

```agda
    data _≺_ : Nat → Nat → Type lzero where
        zero< : {n : Nat} → zero ≺ suc n
        succ< : {n m : Nat} → n ≺ m → (suc n) ≺ (suc m)
```

We then define the `n`th finite ordinal as the subtype of `Nat` consisting of all numbers `m` strictly less than `n`:

```agda
    Fin : Nat → Type lzero
    Fin n = Σ Nat (λ m → m ≺ n)
```

From these data, we can straightforwardly define a polynomial as follows

```agda
    ω : Poly lzero lzero
    ω = (Nat , Fin)
```

If we once again write out the polynomial endofunctor determined by these data $$
    y \mapsto \sum_{n \in \mathbb{N}} y^{\{m \in \mathbb{N} \mid m < n\}}
$$ we see that this functor has a familiar form – it is the *list monad* that maps a type $y$ to the disjoint union of the types of $n$-tuples of elements of $y$, for all $n \in \mathbb{N}$.

As defined, $\omega$ is not a polynomial universe; the type `Nat` is a set, and so for any `n : Nat`, the type `n ≡ n` is contractible, i.e. it has a single inhabitant, while the type of equivalences `Fin n ≃ Fin n` consists of all permutations of `n` elements, so these two types cannot be equivalent. However, we can now use the Rezk completion to obtain a polynomial universe from `ω`.

```agda
    𝔽in : Poly (lsuc lzero) lzero
    𝔽in = Rezk ω
```

If we write out an explicit description of `𝔽in`, we see that it is the subuniverse of types `X` that are merely equivalent to some `Fin n`. In constructive mathematics, these types (they are necessarily sets) are known as *Bishop finite sets*. Hence the polynomial universe obtained by Rezk completion of the list monad is precisely the subuniverse of types spanned by (Bishop) finite sets.