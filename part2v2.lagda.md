```agda
{-# OPTIONS --without-K --rewriting #-}
module part2v2 where

open import part1v2
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
```

# Background on Type Theory, Natural Models & HoTT

We begin with a recap of natural models, dependent type theory, and HoTT, taking this also as an opportunity to introduce the basics of our Agda formalization.

## Dependent Types and their Categorical Semantics

The question "what is a type" is as deep as it is philosophically fraught. For present purposes, however, we need not concern ourselves so much directly with what (dependent) type *are*, as with what they can *do*, and how best to mathematically model this behavior. Suffice it to say, then, that a type specifies rules for both constructing and using the *inhabitants* of that type in arbitrary contexts of usage. Following standard conventions, we use the notation `a : A` to mean that `a` is an inhabitant of type `A`.

In Agda, one example of such a type is the *unit type* `⊤`, which is defined to have a single inhabitant `tt : ⊤`, such that for any other inhabitant `x : ⊤` we must have `x = tt`.

Another type (or rather, family of types) of particular importance is the *universe* of types `Type`, whose inhabitants themsleves represent types.[^1] So e.g. to say that `⊤`, as defined above, is a type, we may simply write `⊤ : Type`.

[^1]: For consistency with the usage of the term "set" in HoTT (whereby sets are types satisfying a certain *truncation* condition, to be explained shortly,) we relabel Agda's universes of types as `Type`, rather than the default `Set`. We also note in passing that, due to size issues, the universe `Type` is not in fact one type, but rather a whole family of types, stratified by a hierarchy of *levels.* However, this structure of levels is not of much concern to us in this paper, so we shall do our best to ignore it.

```agda
Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ
```

Given a type `A`, one may in turn consider families of types `B x` indexed by, or *dependent* upon aribtrary inhabitants `x : A`. In agda, we represent such a type family `B` as a function `A → Type`.

Given a type `A : Type` and a family of types `B : A → Type` as above, two key examples of types we may construct are:

* The *dependent function type* `(x : A) → B x`, whose inhabitants are functions `λ x → f x` such that, for all `a : A`, we have `f a : B a`.
* The *dependent pair type* `Σ A B`, whose inhabitants are of the form `(a , b)` for `a : A` and `b : B a`, such that there are functions `fst : Σ A B → A` and `snd : (p : Σ A B) → B (fst p)`.

Note that in the case where `B` does not depend upon `x : A` (i.e. the variable `x` does not appear in the expression for `B`), these correspond to the more familiar function type `A → B` and pair type `A × B`, respectively. E.g. we can define the Cartesian product of two types `A` and `B` as follows:

```agda
_×_ : ∀ {ℓ κ} (A : Type ℓ) (B : Type κ) → Type (ℓ ⊔ κ)
A × B = Σ A (λ _ → B)
```

In more traditional type-theoretic notation, one might see the rules for these types written as follows: $$ 
\inferrule{}{\Gamma \vdash \top : \mathsf{Type}} \qquad \inferrule{}{\Gamma \vdash \mathsf{tt} : \top} \qquad \inferrule{\Gamma \vdash x : \top}{\Gamma \vdash x = tt}
$$ $$
\inferrule{\Gamma \vdash A : \mathsf{Type}\\ \Gamma, x : A \vdash B[x] : \mathsf{Type}}{\Gamma \vdash \Pi x : A . B[x] : \mathsf{Type}} \qquad \inferrule{\Gamma \vdash A : \mathsf{Type}\\ \Gamma, x : A \vdash B[x] : \mathsf{Type}}{\Gamma \vdash \Sigma x : A . B[x] : \mathsf{Type}}
$$ $$
\inferrule{\Gamma, x : A \vdash f[x] : B[x]}{\Gamma \vdash \lambda x . f[x] : \Pi x : A . B[x]} \qquad \inferrule{\Gamma \vdash a : A\\ \Gamma \vdash b : B[a]}{\Gamma \vdash (a , b) : \Sigma x : A . B[x]}
$$ $$
\inferrule{\Gamma \vdash f : \Pi x : A . B[x]\\ \Gamma \vdash a : A}{\Gamma \vdash f a : B[a]} \qquad \inferrule{\Gamma \vdash p : \Sigma x : A . B[x]}{\Gamma \vdash \pi_1(p) : A} \quad \inferrule{\Gamma \vdash p : \Sigma x : A . B[x]}{\Gamma \vdash \pi_2(p) : B[\pi_1(p)]}
$$ $$
(\lambda x . f[x]) a = f[a] \qquad \pi_1(a , b) = a \quad \pi_2(a , b) = b
$$ $$
f = \lambda x . fx \qquad p = (\pi_1(p) , \pi_2(p))
$$

The constructors $\lambda$ and $(- , -)$ are called the *introduction* forms of $\Pi x : A . B[x]$ and $\Sigma x : A . B[x]$, while $f a$ and $\pi_1(p), ~ \pi_2(p)$ are called the *elimination* forms of these types, respectively. One may wonder why all typing judgments in the above rules have been decorated with annotations of the form $\Gamma \vdash$, for some $\Gamma$. In these cases, $\Gamma$ is the *context* of the corresponding judgment, used to keep track of the types of variables that may appear in that judgment.

Although contexts may seem rather trivial from a syntactic perspective, they are key to understanding the categorical semantics of dependent type theory. In particular, when modelling a dependent type theory as a category, it is the *contexts* which form the objects of this category, with morphisms between contexts being *substitutions* of terms in the domain context for the variables of the codomain context. A type $A$ dependent upon variables in a context $\Gamma$ is then interpreted as a morphism (i.e. substitution) $\Gamma, x : A \to \Gamma$, whose domain represents the context $\Gamma$ extended with a variable of type $A$. We then interpret a term $a$ of type $A$ in context $\Gamma$ as a *section* of the display map representing $A$, i.e. $$
\begin{tikzcd}
	\Gamma & {\Gamma, x : A} \\
	& \Gamma
	\arrow["a", from=1-1, to=1-2]
	\arrow[Rightarrow, no head, from=1-1, to=2-2]
	\arrow["A", from=1-2, to=2-2]
\end{tikzcd}
$$ Hence for each context $\Gamma$, there is a category $\mathbf{Ty}[\Gamma]$, which is the full subcategory of the slice category $\mathcal{C}/\Gamma$ consisting of all display maps, wherein objects correspond to types in context $\Gamma$, and morphisms correspond to terms.

In typical categorical semantics, given a substitution $f : \Gamma \to \Delta$, and a type $A : \Delta, x : A \to \Delta$, we then interpret the action of $f$ on $A$ as a pullback: $$
\begin{tikzcd}
	{\Gamma, x : A[f]} & {\Delta, x : A} \\
	\Gamma & \Delta
	\arrow[from=1-1, to=1-2]
	\arrow["{A[f]}"', from=1-1, to=2-1]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=2-2]
	\arrow["A", from=1-2, to=2-2]
	\arrow["f"', from=2-1, to=2-2]
\end{tikzcd}
$$ In particular, then, any display map $A : \Gamma, x : A \to \Gamma$ induces a functor $\mathbf{Ty}[\Gamma] \to \mathbf{Ty}[\Gamma, x : A]$ by substitution along $A$. The left and right adjoints to this functor (if they exist) then correspond to dependent pair and dependent function types, respectively.

So far, we have told a pleasingly straightforward story of how to interpret the syntax of dependent type theory categorically. Unfortunately, this story is a fantasy, and the interpretation of type-theoretic syntax into categorical semantics sketched above is unsound, as it stands. The problem in essentials is that, in the syntax of type theory, substitution is strictly associative – i.e. given substitutions $f : \Gamma \to \Delta$ and $g : \Delta \to \Theta$ and a type `A`, we have $A[g][f] = A[g[f]]$; however, in the above categorical semantics, such iterated substitution is interpreted via successively taking pullbacks, which is in general only associative up to isomorphism. It seems, then, that something more is needed to account for this kind of *strictness* in the semantics of dependent type theory. It is precisely this problem which natural models exist to solve.

## Natural Models

The key insight of Awodey in formulating the notion of a natural model is that the problem of strictness in the semantics of type theory has, in a sense, already been solved by the notion of *type universes*, such as `Type` as introduced above. Given a universe of types $\mathcal{U}$, rather than representing dependent types as display maps, and substitution as pullback, we can simply represent a family of types $B[x]$ dependent upon a type $A$ as a function $A \to \mathcal{U}$, with substitution then given by precomposition, which is automatically strictly associative.

To interpret the syntax of dependent type theory in a category $\mathcal{C}$ of contexts and substitutions, it therefore suffices to *embed* $\mathcal{C}$ into a category whose type-theoretic internal language posesses such a universe whose types correspond to those of $\mathcal{C}$. For this purpose, we work in the category of *prehseaves* $\mathbf{Set}^{\mathcal{C}^{op}}$, with the embedding $\mathcal{C} \hookrightarrow \mathbf{Set}^{\mathcal{C}^{op}}$ being nothing other than the Yoneda embedding.

The universe $\mathcal{U}$ is then given by an object of $\mathbf{Set}^{\mathcal{C}^{op}}$, i.e. an assignment, to each context $\Gamma$, of a set $\mathsf{Ty}[\Gamma]$ of types in context $\Gamma$, with functions $\mathsf{Ty}[\Delta] \to \mathsf{Ty}[\Gamma]$ for each substitution $f : \Gamma \to \Delta$ that compose associatively, together with a $\mathcal{U}$-indexed family of objects $u \in \mathbf{Set}^{\mathcal{C}^{op}}/\mathcal{U}$, i.e. a natural transformation $u : \mathcal{U}_\bullet \Rightarrow \mathcal{U}$, where for each context $\Gamma$ and type $A \in \mathsf{Ty}[\Gamma]$, the fibre of $u_\Gamma$ over $A$ is the set $\mathsf{Tm}[\Gamma,A]$ of inhabitants of $A$ in context $\Gamma$.

The condition that all types in $\mathcal{U}$ "belong to $\mathcal{C}$", in an appropriate sense, can then be expressed by requiring $u$ to be *representable*, i.e. for any representable $\gamma \in \mathbf{Set}^{\mathcal{C}^{op}}$ with a natural transformation $\alpha : \gamma \Rightarrow \mathcal{U}$, the pullback $$
\begin{tikzcd}
	{\mathcal{\gamma} \times_{\alpha, u} \mathcal{U}_\bullet} & {\mathcal{U}_\bullet} \\
	\gamma & {\mathcal{U}}
	\arrow[Rightarrow, from=1-1, to=1-2]
	\arrow["{u[\alpha]}"', Rightarrow, from=1-1, to=2-1]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=2-2]
	\arrow["u", Rightarrow, from=1-2, to=2-2]
	\arrow["\alpha"', Rightarrow, from=2-1, to=2-2]
\end{tikzcd}
$$ of $u$ along $\alpha$ is representable.

The question, then, is how to express that $\mathcal{C}$ has dependent pair types, dependent function types, etc., in terms of the structure of $u$. A further insight of Awodey, toward answering this question, is that $u$ gives rise to a functor (indeed, a *polynomial functor*) $\overline{u} : \mathbf{Set}^{\mathcal{C}^{op}} \to \mathbf{Set}^{\mathcal{C}^{op}}$, defined as follows $$
\overline{u}(P)(\Gamma) = \sum_{A : \mathsf{Ty}[\Gamma]} P(\Gamma)^{\mathsf{Tm}[\Gamma, A]}
$$ and much of the type-theoretic structure of $u$ can be accounted for in terms of this functor. For instance (for reasons to be explained shortly), dependent pair types are given by a natural transformation $\sigma : \overline{u} \circ \overline{u} \Rightarrow \overline{u}$, that is *Cartesian* in that, for every $\alpha : P \Rightarrow Q$, the following naturality square is a pullback $$
\begin{tikzcd}
	{\overline{u}(\overline{u}(P))} & {\overline{u}(\overline{u}(Q))} \\
	{\overline{u}(P)} & {\overline{u}(Q)}
	\arrow["{\overline{u}(\overline{u}(\alpha))}", Rightarrow, from=1-1, to=1-2]
	\arrow["{\sigma_P}"', Rightarrow, from=1-1, to=2-1]
	\arrow["\lrcorner"{anchor=center, pos=0.125}, draw=none, from=1-1, to=2-2]
	\arrow["{\sigma_Q}", Rightarrow, from=1-2, to=2-2]
	\arrow["{\overline{u}(\alpha)}"', Rightarrow, from=2-1, to=2-2]
\end{tikzcd}
$$

A question that arises, then, is what structure such a natural transformation interpreting dependent pair types must possess. It is natural to think that $\sigma$, along with a suitably-chosen natural transformation $Id \Rightarrow \overline{u}$, ought to give $\overline{u}$ the structure of a monad. However, this turns out to be too strong a requirement, as it amounts to asking that $\Sigma x : A . (\Sigma y : B[x] . C[x,y]) = \Sigma (x,y) : (\Sigma x : A . B[x]) . C[x,y]$, when in general this identity only holds up to isomorphism. Hence we seem to have crossed over from Scylla of our semantics for dependent type theory not being strict enough to interpret those identities we expect to hold strictly, to the Charybdis of them now being too strict to interpret the identities we expect to hold only up to isomorphism. It was for this reason that Awodey & Newstead were forced to ultimately go beyond Polynomial functors in their accounts of natural models.

However, another possibility exists to solve this dilemma – to use the language of HoTT itself to reason about such equality-up-to-isomorphism in natural models. For this purpose, rather than taking natural models to be certain (representable) morphisms in $\mathbf{Set}^{\mathcal{C}^{op}}$, we can instead expand the mathematical universe in which these models live to $\mathbf{\infty Grpd}^{\mathcal{C}^{op}}$, which, as an $\infty$-topos, has HoTT as its internal language. Taking advantage of this fact, we can use HoTT itself as a language for studying the semantics of type theory, by postulating an abstract type $\mathcal{U}$ together with a type family $u : \mathcal{U} \to \mathsf{Type}$, corresponding to a representable natural transformation $u : \mathcal{U}_\bullet \Rightarrow \mathcal{U}$ as above.

What remains, then, is to show how the various type-theoretic properties of such natural models can be expressed in terms of polynomial functors in the language of HoTT, and the complex identities to which these give rise. For this purpose, we begin with a recap of the basics of HoTT, before launching into a development of the theory of polynomial functors within HoTT, with an eye toward the latter's use in the study of natural models.

## Homotopy Type Theory

### The Identity Type

Given elements `a,b : A` for some type `A`, the identity type `a ≡ b` is inductively generated from the single constructor `refl : {x : A} → x ≡ x`, witnessing reflexivity of equality.

```agda
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
```

The core insight of Homotopy Type Theory is that the presence of (intensional) identity types in a system of dependent type theory endows each type with the structure of an $\infty$-groupoid, and endows each function between types with the structure of a functor between $\infty$-groupoids, etc. This allows a wealth of higher-categorical properties and structures to be defined and studied *internally* in the language of dependent type theory.

Since an invocation of reflexivity typically occurs at the end of an equality proof, we introduce the notation `□` as a shorthand for `refl` as follows:

```agda
_□ : ∀ {ℓ} {A : Type ℓ} (a : A) → a ≡ a
a □ = refl
```

The inductive generation of `a ≡ b` from `refl` then gives rise to the operation of *transport* that allows an inhabitant of the type `B a` to be converted to an inhabitant of `B b` for any type family `B : (x : A) → Type`.

```agda
transp : ∀ {ℓ κ} {A : Type ℓ} (B : A → Type κ) {a a' : A} 
         → (e : a ≡ a') → B a → B a'
transp B refl b = b
```

Transitivity of equality then follows in the usual way.[^1]:

```agda
_•_ : ∀ {ℓ} {A : Type ℓ} {a b c : A}
      → (a ≡ b) → (b ≡ c) → (a ≡ c)
e • refl = e
```

[^1]: We also take advantage of Agda's support for mixfix notation to present transitivity in such a way as to streamline both the reading and writing of equality proofs:

```agda
_≡〈_〉_ : ∀ {ℓ} {A : Type ℓ} (a : A) {b c : A} 
          → a ≡ b → b ≡ c → a ≡ c
a ≡〈 e 〉 refl = e

comprewrite : ∀ {ℓ} {A : Type ℓ} {a b c : A}
              → (e1 : a ≡ b) (e2 : b ≡ c)
              → (a ≡〈 e1 〉 e2) ≡ (e1 • e2)
comprewrite refl refl = refl

{-# REWRITE comprewrite #-}
```

Symmetry of equality follows similarly:

```agda
sym : ∀ {ℓ} {A : Type ℓ} {a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl
```

As mentioned above, each function `f : A → B` in HoTT is canonically endowed with the structure of a functor between $\infty$-groupoids, where the action of such a function `f` on paths (i.e. elements of the identity type) is as follows:

```agda
ap : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {a a' : A}
     → (f : A → B) → a ≡ a' → (f a) ≡ (f a')
ap f refl = refl
```

By the same token, given a proof `f ≡ g` for two functions `f,g : (x : A) → B x`, it follows that for any `a : A` we have `f a ≡ g a`.

```agda
coAp : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
       → f ≡ g → (x : A) → f x ≡ g x
coAp refl x = refl
```

We additionally have the following "dependent" form of `ap` as above, allowing us to apply a dependent function to both sides of an identity, in a suitable manner:

```agda
apd : ∀ {ℓ0 ℓ1 κ} {A : Type ℓ0} {B : Type ℓ1} {f : A → B}
      → (C : B → Type κ) {a a' : A}
      → (g : (x : A) → C (f x)) → (e : a ≡ a') → transp C (ap f e) (g a) ≡ g a'
apd B f refl = refl
```

To show that two pairs `(a , b)` and `(a' , b')` are equal, it suffices to show that there is an identification `e : a ≡ a'` together with `e' : transp B e b ≡ b'`.

```agda
module PairEq {ℓ κ} {A : Type ℓ} {B : A → Type κ} 
              {a a' : A} {b : B a} {b' : B a'} where

    pairEq : (e : a ≡ a') (e' : transp B e b ≡ b') → (a , b) ≡ (a' , b')
    pairEq refl refl = refl
```

We then have the following laws governing equality proofs for pairs.

```agda
    pairEqβ1 : (e : a ≡ a') (e' : transp B e b ≡ b') → ap fst (pairEq e e') ≡ e
    pairEqβ1 refl refl = refl

    pairEqη : (e : (a , b) ≡ (a' , b')) → pairEq (ap fst e) (apd B snd e) ≡ e
    pairEqη refl = refl

open PairEq public
```

### Equivalences

A pivotal notion, both for HoTT in general, and for the content of this paper, is that of a function `f : A → B` being an *equivalence* of types. The reader familiar with HoTT will know that there are several definitions – all equivalent – of this concept appearing in the HoTT literature. For present purposes, we make use of the *bi-invertible maps* notion of equivalence. Hence we say that a function `f : A → B` is an equivalence if it has both a left inverse and a right inverse:

```agda
isEquiv : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (A → B) → Type (ℓ ⊔ κ)
isEquiv {A = A} {B = B} f = 
      (Σ (B → A) (λ g → (a : A) → g (f a) ≡ a)) 
    × (Σ (B → A) (λ h → (b : B) → f (h b) ≡ b))
```

Straightforwardly, the identity function at each type is an equivalence, and equivalences are closed under composition:

```agda
idIsEquiv : ∀ {ℓ} {A : Type ℓ} → isEquiv {A = A} (λ x → x)
idIsEquiv = ((λ x → x) , (λ x → refl)) , ((λ x → x) , (λ x → refl))

compIsEquiv : ∀ {ℓ0 ℓ1 ℓ2} {A : Type ℓ0} {B : Type ℓ1} {C : Type ℓ2}
              → {g : B → C} {f : A → B} → isEquiv g → isEquiv f
              → isEquiv (λ a → g (f a))
compIsEquiv {g = g} {f = f} 
            ((g' , lg) , (g'' , rg)) 
            ((f' , lf) , (f'' , rf)) =
      ( (λ c → f' (g' c))   
      , λ a → (f' (g' (g (f a))))   ≡〈 ap f' (lg (f a)) 〉 
              (f' (f a)             ≡〈 lf a 〉 
              (a                    □))) 
    , ((λ c → f'' (g'' c)) 
      , λ c → (g (f (f'' (g'' c)))) ≡〈 ap g  (rf (g'' c)) 〉 
              (g (g'' c)            ≡〈 rg c 〉
              (c                    □)))
```

A closely-related notion to equivalence is that of a function `f` being an *isomorphism*, i.e. having a single two-sided inverse:

```agda
Iso : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (A → B) → Type (ℓ ⊔ κ)
Iso {A = A} {B = B} f = 
    (Σ (B → A) (λ g → ((a : A) → g (f a) ≡ a) 
                    × ((b : B) → f (g b) ≡ b)))
```

One might be inclined to wonder, then, why we bother to define equivalence via the seemingly more complicated notion of having both a left and a right inverse when the familiar notion of isomorphism can just as well be defined, as above. The full reasons for this are beyond the scope of this paper, though see \cite{hottbook} for further discussion. Suffice it to say that, for subtle reasons due to the higher-categorical structure of types in HoTT, the plain notion of isomorphism given above is not a *good* notion of equivalence, whereas that of bi-invertible maps is. In particular, the type `Iso f` is not necessarily a proposition for arbitrary `f`, whereas `isEquiv f` is.

We may nonetheless move more-or-less freely back and forth between the notions of equivalence and isomorphism given above, thanks to the following functions, which allow us to convert isomorphisms to equivalences and vice versa:

```agda
module Iso↔Equiv {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B} where

    Iso→isEquiv : Iso f → isEquiv f
    Iso→isEquiv (g , l , r) = ((g , l) , (g , r))

    isEquiv→Iso : isEquiv f → Iso f
    isEquiv→Iso ((g , l) , (h , r)) = 
        h , (λ x → (h (f x))        ≡〈 sym (l (h (f x))) 〉 
                   (g (f (h (f x))) ≡〈 ap g (r (f x)) 〉
                   ((g (f x))       ≡〈 l x 〉 
                   (x □)))) , r

open Iso↔Equiv public
```

And by the above translation between equivalences and isomorphisms, each equivalence has a corresponding inverse map in the opposite direction, which is itself an equivalence:

```agda
module InvEquiv {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B} where

    inv : isEquiv f → B → A
    inv (_ , (h , _)) = h

    isoInv : (isof : Iso f) → Iso (fst isof)
    isoInv (g , l , r) = (f , r , l)

    invIsEquiv : (ef : isEquiv f) → isEquiv (inv ef)
    invIsEquiv ef = Iso→isEquiv (isoInv (isEquiv→Iso ef))
    
open InvEquiv public
```

We note that, for each type family `B : A → Type`, the map `B a → B a'` induced by transport along `e : a ≡ a'` for any `a, a' : A` is an equivalence with inverse given by transport along `sym e`, as follows:

```agda
module TranspEquiv {ℓ κ} {A : Type ℓ} {B : A → Type κ} {a b : A} (e : a ≡ b) where

    syml : (x : B a) → transp B (sym e) (transp B e x) ≡ x
    syml x rewrite e = refl

    symr : (y : B b) → transp B e (transp B (sym e) y) ≡ y
    symr y rewrite e = refl

    transpIsEquiv : isEquiv {A = B a} {B = B b} (λ x → transp B e x)
    transpIsEquiv = Iso→isEquiv ((λ x → transp B (sym e) x) , (syml , symr))

open TranspEquiv public
```

### Truncation, Bracket Types & Factorization

We say that a type `A` is:

1. *contractible* (aka (-2)-truncated) if `A` is uniquely inhabited
2. a (mere) *proposition* (aka (-1)-truncated) if any two elements of `A` are identical
3. a *set* (aka 0-truncated) if for any `a,b : A`, the type `a ≡ b` is a proposition.

```agda
isContr : ∀ {ℓ} → Type ℓ → Type ℓ
isContr A = Σ A (λ a → (b : A) → a ≡ b)

isProp : ∀ {ℓ} → Type ℓ → Type ℓ
isProp A = {a b : A} → a ≡ b

isSet : ∀ {ℓ} → Type ℓ → Type ℓ
isSet A = (a b : A) → isProp (a ≡ b)
```

We additionally postulate the existence of a *propositional truncation,* or *bracket type* operation, that takes a type `A` to the least proposition (wrt entailment) entailed by inhabitation of `A`.

```agda
postulate
    ∥_∥ : ∀ {ℓ} (A : Type ℓ) → Type lzero
    in∥-∥ : ∀ {ℓ} {A : Type ℓ} → A → ∥ A ∥
    ∥-∥IsProp : ∀ {ℓ} {A : Type ℓ} → isProp (∥ A ∥)
    ∥-∥≡Contr : ∀ {ℓ} {A : Type ℓ} {a b : ∥ A ∥} {e : a ≡ b} → ∥-∥IsProp ≡ e
    ∥-∥Rec : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ}
            → isProp B → (A → B) → ∥ A ∥ → B
```

When the type `∥ A ∥` is inhabited, we say that `A` is *merely* inhabited.

From this operation on types, we straightforwardly obtain the higher analogue of the usual epi-mono factorization system on functions between sets, as follows:

```agda
module Epi-Mono {ℓ κ} {A : Type ℓ} {B : Type κ} (f : A → B) where
```

We say that a function `f : A → B` is *injective* (i.e. a monomorphism), if for all `a , b : A` the map `ap f : a ≡ b → f a ≡ f b` is an equivalence

```agda
    isMono : Type (ℓ ⊔ κ)
    isMono = {a b : A} → isEquiv (ap {a = a} {a' = b} f)
```

Given an element `b : B`, the *fibre* of `f` at `b` is the type of elements of `a` equipped with a proof of `f a ≡ b`:

```agda
    Fibre : B → Type (ℓ ⊔ κ)
    Fibre b = Σ A (λ a → f a ≡ b)
```

We then say that `f` is *surjective* (i.e. an epimorphism), if all of its fibres are merely inhabited.

```agda
    isEpi : Type κ
    isEpi = (b : B) → ∥ Fibre b ∥

open Epi-Mono public

module EMFactor {ℓ κ} {A : Type ℓ} {B : Type κ} (f : A → B) where
```

Given a function `f`, its *image* is the type of elements of `B` whose fibres are merely inhabited.

```agda
    Im : Type κ
    Im = Σ B (λ b → ∥ Fibre f b ∥)
```

Every function `f` can then be factored into a (-1)-connected map onto its image followed by a (-1)-truncated map onto its codomain:

```agda
    factor1 : A → Im
    factor1 a = (f a) , in∥-∥ (a , refl)

    factor2 : Im → B
    factor2 (b , _) = b

    factor≡ : (a : A) → factor2 (factor1 a) ≡ f a
    factor≡ a = refl

    factor1IsEpi : isEpi factor1
    factor1IsEpi (b , x) = 
        ∥-∥Rec ∥-∥IsProp 
              (λ {(a , refl) → in∥-∥ (a , pairEq refl ∥-∥IsProp)}) 
              x

    factor2IsMono : isMono factor2
    factor2IsMono {a = (a , α)} {b = (b , β)} = 
        Iso→isEquiv ( (λ e → pairEq e ∥-∥IsProp) 
                    , ( (λ e → (pairEq (ap factor2 e) ∥-∥IsProp) 
                               ≡〈 (ap (pairEq (ap factor2 e)) ∥-∥≡Contr) 〉 
                               ( _ 
                               ≡〈 pairEqη e 〉 
                               (e □)))
                      , λ e → pairEqβ1 e ∥-∥IsProp))

open EMFactor public
```

Some additional facts about the identity type, that will be used in formalizing the results of this paper, are given in Appendix A.