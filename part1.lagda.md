---
title: Polynomial Universes and Dependent Types
author:
    - C.B. Aberlé
    - David I. Spivak
documentclass: memoir
classoption:
    - 11pt
    - oneside
    - article
---

\begin{abstract}

Awodey, later with Newstead, showed how polynomial pseudomonads $(u,\1,\Sigma)$ with extra structure (termed "natural models" by Awodey) hold within them the syntax and rules for dependent type theory. Their work presented these ideas clearly but ultimately led them outside of the category of polynomial functors in order to explain all of the structure possessed by such models of type theory.

This paper builds off that work---explicating the syntax and rules for dependent type theory by axiomatizing them \emph{entirely} in the language of polynomial functors. In order to handle the higher-categorical coherences required for such an explanation, we work with polynomial functors internally in the language of Homotopy Type Theory, which allows for higher-dimensional structures such as pseudomonads, etc. to be expressed purely in terms of the structure of a suitably-chosen $\infty$-category of polynomial functors. The move from set theory to Homotopy Type Theory thus has a twofold effect of enabling a simpler exposition of natural models, which is at the same time amenable to formalization in a proof assistant, such as Agda.

Moreover, the choice to remain firmly within the setting of polynomial functors reveals many additional structures of natural models that were otherwise left implicit or not considered by Awodey \& Newstead. Chief among these, we highlight the fact that every polynomial pseudomonad $(u,\1,\Sigma)$ as above that is also equipped with structure to interpret dependent product types gives rise to a self-distributive law $u\tri u\to u\tri u$, which witnesses the usual distributive law of dependent products over dependent sums.

\end{abstract}

# Introduction

Dependent type theory \cite{martin-lof1975intuitionistic} was founded by Per Martin-Löf in 1975 (among others) to formalize constructive mathematics. The basic idea is that the \emph{order of events} is fundamental to the mathematical story arc: when playing out any specific example story in that arc, the beginning of the story affects not only the later events, but even the very terms with which the later events will be described. For example, in the story arc of conditional probability, one may say ``now if the set $P$ that we are asked to condition on happens to have measure zero, we must stop; but assuming that's not the case then the result will be a new probability measure.'' Here the story teller is saying that no terms will describe what happens if $P$ has measure zero, whereas otherwise the terms of standard probability will apply.

Dependent types form a logical system with syntax, rules of computation, and methods of deduction. In \cite{awodey2014natural,awodey2018polynomial}, Awodey and later Newstead show that there is a strong connection between dependent type theory and polynomial functors, via their concept of *natural models*, which cleanly solve the problem of *strictififying* certain identities that typically hold only up to isomorphism in arbitrary categories, but must hold *strictly* in order for these to soundly model dependent type theory. The solution to this problem offered by Awodey and Newstead makes use of the type-theoretic concept of a *universe*. Such universes then turn out to naturally be regarded as polynomial functors on a suitably-chosen category of presheaves, satisfying a certain *representability* condition.

Although the elementary structure of natural models is thus straightforwardly described by considering them as objects in the category of polynomial functors, Awodey and Newstead were ultimately led outside of this category in order to fully explicate those parts of natural models that require identities to hold only *up to isomorphism*, rather than strictly. There is thus an evident tension between *strict* and *weak* identities that has not yet been fully resolved in the story of natural models. In the present work, we build on Awodey and Newstead's work to fully resolve this impasse by showing how type universes can be fully axiomatized in terms of polynomial functors, by working with polynomial functors internally in the language of *Homotopy Type Theory* (HoTT). We thus come full circle from Awodey's original motivation to develop natural models *of* Homotopy Type Theory, to describing natural models *in* Homotopy Type Theory.

The ability for us to tell the story of natural models as set entirely in the category of polynomial functors has a great simplifying effect upon the resultant theory, and reveals many additional structures, both of polynomial universes, and of the category of polynomial functors as a whole. As an illustration of this, we show how every polynomial universe $u$, regarded as a polynomial pseudomonad with additional structure, gives rise to self-distributive law $u\tri u\to u\tri u$, which in particular witnesses the usual distributive law of dependent products over dependent sums.

Moreover, the move from set theory to HoTT as a setting in which to tell this story enables new tools to be applied for its telling. In particular, the account of polynomial universes we develop is well-suited to formalization in a proof assistant, and we present such a formalization in Agda. This paper is thus itself a literate Agda document in which all results have been fully formalized and checked for validity.

```agda
{-# OPTIONS --without-K --rewriting #-}
module part1 where

open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
```

The structure of this paper is as follows:

# Background on Type Theory, Natural Models & HoTT

We begin with a recap of natural models, dependent type theory, and HoTT, taking this also as an opportunity to introduce the basics of our Agda formalization.

## Dependent Types and their Categorical Semantics

The question "what is a type" is as deep as it is philosophically fraught. For present purposes, however, we need not concern ourselves so much directly with what (dependent) type *are*, as with what they can *do*, and how best to mathematically model this behavior. Suffice it to say, then, that a type specifies rules for both constructing and using the *inhabitants* of that type in arbitrary contexts of usage. Following standard conventions, we use the notation `a : A` to mean that `a` is an inhabitant of type `A`.

In Agda, one example of such a type is the *unit type* `⊤`, which is defined to have a single inhabitant `tt : ⊤`, such that for any other inhabitant `x : ⊤` we must have `x = tt`.

Another type (or rather, family of types) of particular importance is the *universe* of types `Type`, whose inhabitants themsleves represent types.[^1] So e.g. to say that `⊤`, as defined above, is a type, we may simply write `⊤ : Type`.

[^1]: For consistency with the usage of the term "set" in HoTT (whereby sets are types satisfying a certain *truncation* condition, to be explained shortly,) we relabel Agda's universes of types as `Type`, rather than the default `Set`.

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

So far, we have told a pleasingly straightforward story of how to interpret the syntax of dependent type theory categorically. Unfortunately, this story is a fantasy, and the interpretation of type-theoretic syntax into categorical semantics sketched above is unsound, as it stands. The problem in essentials is that, in the syntax of type theory, substitution is strictly associative – i.e. given substitutions $f : \Gamma \to \Delta$ and $g : \Delta \to \Theta$ and a type `A`, we have $A[g][f] = A[g[f]]$; however, in the above categorical semantics, such iterated substitution is interpreted via successively taking pullbacks, which is in general only associative up to isomorphism. It seems, then, that something more is needed to account for this kind of *strictness* in the semantics of dependent type theory. [^2] It is precisely this problem which natural models exist to solve.

[^2]: Something something Beck-Chevalley...

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

Transitivity of equality then follows in the usual way. Note, however, that we take advantage of Agda's support for mixfix notation to present transitivity in such a way as to streamline both the reading and writing of equality proofs:

```agda
_≡〈_〉_ : ∀ {ℓ} {A : Type ℓ} (a : A) {b c : A} 
          → a ≡ b → b ≡ c → a ≡ c
a ≡〈 e 〉 refl = e
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

Moreover, to show that two pairs `(a , b)` and `(a' , b')` are equal, it suffices to show that there is an identification `e : a ≡ a'` together with `e' : transp B e b ≡ b'`.

```agda
pairEq : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} 
         → {a a' : A} {b : B a} {b' : B a'}
         → (e : a ≡ a') (e' : transp B e b ≡ b') 
         → (a , b) ≡ (a' , b')
pairEq refl refl = refl
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
    ∥-∥Rec : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ}
            → isProp B → (A → B) → ∥ A ∥ → B
```

When the type `∥ A ∥` is inhabited, we say that `A` is *merely* inhabited.

From this operation on types, we straightforwardly obtain the higher analogue of the usual epi-mono factorization system on functions between sets, as follows:

Given a function `f : A → B` and an element `b : B`, the *fibre* of `f` at `b` is the type of elements of `a` equipped with a proof of `f a ≡ b`:

```agda
Fibre : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (A → B) → B → Type (ℓ ⊔ κ)
Fibre {A = A} f b = Σ A (λ a → f a ≡ b)
```

By the same token, given such an `f`, its *image* is the type of elements of `B` whose fibres are merely inhabited.

```agda
Im : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (A → B) → Type κ
Im {B = B} f = Σ B (λ b → ∥ Fibre f b ∥)
```

We say that `f` is *(-1)-truncated* (i.e. a monomorphism), if for each `b : B`, the fibre of `f` at `b` is a proposition.

```agda
isMono : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (A → B) → Type (ℓ ⊔ κ)
isMono {B = B} f = (b : B) → isProp (Fibre f b)
```

Likewise, we say that `f` is *(-1)-connected* (i.e. an epimorphism), if all of its fibres are merely inhabited.

```agda
isEpi : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (A → B) → Type κ
isEpi {B = B} f = (b : B) → ∥ Fibre f b ∥
```

Every function `f` can then be factored into a (-1)-connected map onto its image followed by a (-1)-truncated map onto its codomain:

```agda
factor1 : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (f : A → B) → A → Im f
factor1 f a = (f a) , in∥-∥ (a , refl)

factor2 : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (f : A → B) → Im f → B
factor2 f (b , _) = b

factor≡ : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} 
          → (f : A → B) (a : A) → factor2 f (factor1 f a) ≡ f a
factor≡ f a = refl

factor1IsEpi : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ}
               → (f : A → B) → isEpi (factor1 f)
factor1IsEpi f (b , x) = 
    ∥-∥Rec ∥-∥IsProp 
          (λ {(a , refl) → in∥-∥ (a , pairEq refl ∥-∥IsProp)}) 
          x

factor2IsMono : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ}
                → (f : A → B) → isMono (factor2 f)
factor2IsMono f b {a = ((b' , x) , refl)} {b = ((b'' , x') , refl)} = 
    pairEq (pairEq refl ∥-∥IsProp) (lemma ∥-∥IsProp)
    where lemma : (e : x ≡ x') → transp (λ a → factor2 f a ≡ b) 
                                        (pairEq refl e) refl ≡ refl
          lemma refl = refl
```

### Equivalences

A pivotal notion, both for HoTT in general, and for the content of this paper, is that of a function `f : A → B` being an *equivalence* of types. The reader familiar with HoTT will know that there are several definitions – all equivalent – of this concept appearing in the HoTT literature. For present purposes, we make use of the *bi-invertible maps* notion of equivalence. Hence we say that a function `f : A → B` is an equivalence if it has both a left inverse and a right inverse:

```agda
isEquiv : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (A → B) → Type (ℓ ⊔ κ)
isEquiv {A = A} {B = B} f =
      (Σ (B → A) (λ g → (a : A) → g (f a) ≡ a)) 
    × (Σ (B → A) (λ h → (b : B) → f (h b) ≡ b))
```

A closely-related notion is that of a function `f` being an *isomorphism*, i.e. having a single two-sided inverse:

```agda
Iso : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} → (A → B) → Type (ℓ ⊔ κ)
Iso {A = A} {B = B} f =
    (Σ (B → A) (λ g → ((a : A) → g (f a) ≡ a) 
                    × ((b : B) → f (g b) ≡ b)))
```

One might be inclined to wonder, then, why we bother to define equivalence via the seemingly more complicated notion of having both a left and a right inverse when the familiar notion of isomorphism can just as well be defined, as above. The full reasons for this are beyond the scope of this paper, though see \cite{hottbook} for further discussion. Suffice it to say that, for subtle reasons due to the higher-categorical structure of types in HoTT, the plain notion of isomorphism given above is not a *good* notion of equivalence, whereas that of bi-invertible maps is. In particular, the type `Iso f` is not necessarily a proposition for arbitrary `f`, whereas `isEquiv f` is.

We may nonetheless move more-or-less freely back and forth between the notions of equivalence and isomorphism given above, thanks to the following functions, which allow us to convert isomorphisms to equivalences and vice versa:

```agda
Iso→isEquiv : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B} 
              → Iso f → isEquiv f
Iso→isEquiv (g , l , r) = ((g , l) , (g , r))

isEquiv→Iso : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B} 
              → isEquiv f → Iso f
isEquiv→Iso {f = f} ((g , l) , (h , r)) = 
    h , (λ x → (h (f x))        ≡〈 sym (l (h (f x))) 〉 
               (g (f (h (f x))) ≡〈 ap g (r (f x)) 〉
               ((g (f x))       ≡〈 l x 〉 
               (x □)))) , r
```

Straightforwardly, the identity function at each type is an equivalence, and equivalences are closed under composition:

```agda
idIsEquiv : ∀ {ℓ} {A : Type ℓ} → isEquiv {A = A} (λ x → x)
idIsEquiv = ((λ x → x) , (λ x → refl)) , ((λ x → x) , (λ x → refl))

compIsEquiv : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
              → (g : B → C) (f : A → B) → isEquiv g → isEquiv f
              → isEquiv (λ a → g (f a))
compIsEquiv g f ((g' , lg) , (g'' , rg)) ((f' , lf) , (f'' , rf)) = 
      ( (λ c → f' (g' c))   
      , λ a → (f' (g' (g (f a))))   ≡〈 ap f' (lg (f a)) 〉 
              (f' (f a)             ≡〈 lf a 〉 
              (a                    □))) 
    , ((λ c → f'' (g'' c)) 
      , λ c → (g (f (f'' (g'' c)))) ≡〈 ap g  (rf (g'' c)) 〉 
              (g (g'' c)            ≡〈 rg c 〉
              (c                    □)))
```

And by the above translation between equivalences and isomorphisms, each equivalence has a corresponding inverse map in the opposite direction, which is itself an equivalence:

```agda
inv : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B} → isEquiv f → B → A
inv (_ , (h , _)) = h

isoInv : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B}
         → (isof : Iso f) → Iso (fst isof)
isoInv {f = f} (g , l , r) = (f , r , l)

invIsEquiv : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B}
             → (ef : isEquiv f) → isEquiv (inv ef)
invIsEquiv ef = Iso→isEquiv (isoInv (isEquiv→Iso ef))
```

We close this section by noting that, for each type family `B : A → Type`, the map `B a → B a'` induced by transport along `e : a ≡ a'` for any `a, a' : A` is an equivalence with inverse given by transport along `sym e`, as follows:

```agda
syml : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {a b : A}
       → (e : a ≡ b) (x : B a) → transp B (sym e) (transp B e x) ≡ x
syml refl x = refl

symr : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {a b : A}
       → (e : a ≡ b) (y : B b) → transp B e (transp B (sym e) y) ≡ y
symr refl x = refl

transpIsEquiv : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {a b : A} (e : a ≡ b)
                → isEquiv {A = B a} {B = B b} (λ x → transp B e x)
transpIsEquiv {B = B} e = Iso→isEquiv ((λ x → transp B (sym e) x) , (syml e , symr e))
```

And...

```agda
transpAp : ∀ {ℓ ℓ' κ} {A : Type ℓ} {A' : Type ℓ'} {a b : A}
           → (B : A' → Type κ) (f : A → A') (e : a ≡ b) (x : B (f a))
           → transp (λ x → B (f x)) e x ≡ transp B (ap f e) x
transpAp B f refl x = refl

≡siml : ∀ {ℓ} {A : Type ℓ} {a b : A}
        → (e : a ≡ b) → refl ≡ (b ≡〈 sym e 〉 e)
≡siml refl = refl

≡idr : ∀ {ℓ} {A : Type ℓ} {a b : A}
       → (e : a ≡ b) → e ≡ (a ≡〈 refl 〉 e)
≡idr refl = refl

conj : ∀ {ℓ} {A : Type ℓ} {a b c d : A}
       → (e1 : a ≡ b) (e2 : a ≡ c) (e3 : b ≡ d) (e4 : c ≡ d)
       → (a ≡〈 e1 〉 e3) ≡ (a ≡〈 e2 〉 e4)
       → e3 ≡ (b ≡〈 sym e1 〉(a ≡〈 e2 〉 e4))
conj e1 e2 refl refl refl = ≡siml e1

nat : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f g : A → B} {a b : A}
      → (α : (x : A) → f x ≡ g x) (e : a ≡ b)
      → ((f a) ≡〈 α a 〉 (ap g e)) ≡ ((f a) ≡〈 ap f e 〉 (α b))
nat {a = a} α refl = ≡idr (α a)

cancel : ∀ {ℓ} {A : Type ℓ} {a b c : A}
         → (e1 e2 : a ≡ b) (e3 : b ≡ c)
         → (a ≡〈 e1 〉 e3) ≡ (a ≡〈 e2 〉 e3)
         → e1 ≡ e2
cancel e1 e2 refl refl = refl

apId : ∀ {ℓ} {A : Type ℓ} {a b : A}
       → (e : a ≡ b) → ap (λ x → x) e ≡ e
apId refl = refl

apComp : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''} {a b : A}
         → (f : A → B) (g : B → C) (e : a ≡ b)
         → ap (λ x → g (f x)) e ≡ ap g (ap f e)
apComp f g refl = refl

apHtpy : ∀ {ℓ} {A : Type ℓ} {a : A}
         → (i : A → A) (α : (x : A) → i x ≡ x)
         → ap i (α a) ≡ α (i a)
apHtpy {a = a} i α = 
    cancel (ap i (α a)) (α (i a)) (α a) 
           ((i (i a) ≡〈 ap i (α a) 〉 α a) 
           ≡〈 sym (nat α (α a)) 〉 
           ((i (i a) ≡〈 α (i a) 〉 ap (λ z → z) (α a)) 
           ≡〈 ap (λ e → i (i a) ≡〈 α (i a) 〉 e) (apId (α a)) 〉 
           ((i (i a) ≡〈 α (i a) 〉 α a) □)))

HAdj : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ}
       → (A → B) → Set (ℓ ⊔ κ)
HAdj {A = A} {B = B} f =
    Σ (B → A) (λ g → 
      Σ ((x : A) → g (f x) ≡ x) (λ η → 
        Σ ((y : B) → f (g y) ≡ y) (λ ε → 
          (x : A) → ap f (η x) ≡ ε (f x))))

Iso→HAdj : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B}
           → Iso f → HAdj f
Iso→HAdj {f = f} (g , η , ε) =
    g , (η 
    , ( (λ y → 
           f (g y)         ≡〈 sym (ε (f (g y))) 〉 
          (f (g (f (g y))) ≡〈 ap f (η (g y)) 〉 
          (f (g y)         ≡〈 ε y 〉 
          (y               □)))) 
      , λ x → conj (ε (f (g (f x)))) (ap f (η (g (f x)))) 
                   (ap f (η x)) (ε (f x)) 
                   (((f (g (f (g (f x)))) ≡〈 ε (f (g (f x))) 〉 ap f (η x))) 
                    ≡〈 nat (λ z → ε (f z)) (η x) 〉 
                    (((f (g (f (g (f x)))) ≡〈 ap (λ z → f (g (f z))) (η x) 〉 ε (f x))) 
                    ≡〈 ap (λ e → (f (g (f (g (f x)))) ≡〈 e 〉 ε (f x))) 
                          ((ap (λ z → f (g (f z))) (η x)) 
                           ≡〈 apComp (λ z → g (f z)) f (η x) 〉 
                           ((ap f (ap (λ z → g (f z)) (η x))) 
                           ≡〈 ap (ap f) (apHtpy (λ z → g (f z)) η) 〉 
                           (ap f (η (g (f x))) □))) 〉 
                    (((f (g (f (g (f x)))) ≡〈 ap f (η (g (f x))) 〉 ε (f x))) □)))))

pairEquiv1 : ∀ {ℓ ℓ' κ} {A : Type ℓ} {A' : Type ℓ'} {B : A' → Type κ}
             → (f : A → A') → isEquiv f
             → isEquiv {A = Σ A (λ x → B (f x))} {B = Σ A' B} 
                       (λ (x , y) → (f x , y))
pairEquiv1 {A = A} {A' = A'} {B = B} f ef =
  Iso→isEquiv
    ( (λ (x , y) → (g x , transp B (sym (ε x)) y))
    , ( (λ (x , y) → pairEq (η x) (lemma x y)) 
      , λ (x , y) → pairEq (ε x) (symr (ε x) y) ) )
  where
    g : A' → A
    g = fst (Iso→HAdj (isEquiv→Iso ef))
    η : (x : A) → g (f x) ≡ x
    η = fst (snd (Iso→HAdj (isEquiv→Iso ef)))
    ε : (y : A') → f (g y) ≡ y
    ε = fst (snd (snd (Iso→HAdj (isEquiv→Iso ef))))
    ρ : (x : A) → ap f (η x) ≡ ε (f x)
    ρ = snd (snd (snd (Iso→HAdj (isEquiv→Iso ef))))
    lemma : (x : A) (y : B (f x))
            → transp (λ z → B (f z)) (η x)
                     (transp B (sym (ε (f x))) y)
              ≡ y
    lemma x y = (transp (λ z → B (f z)) (η x) 
                        (transp B (sym (ε (f x))) y)) 
                ≡〈 transpAp B f (η x) 
                            (transp B (sym (ε (f x))) y) 〉 
                ( transp B (ap f (η x)) 
                           (transp B (sym (ε (f x))) y) 
                ≡〈 ap (λ e → transp B e 
                                (transp B (sym (ε (f x))) y)) 
                      (ρ x) 〉 
                ( (transp B (ε (f x)) 
                          (transp B (sym (ε (f x))) y)) 
                ≡〈 (symr (ε (f x)) y) 〉 
                (y □)))

pairEquiv2 : ∀ {ℓ κ κ'} {A : Type ℓ} {B : A → Type κ} {B' : A → Type κ'}
             → (g : (x : A) → B x → B' x) → ((x : A) → isEquiv (g x))
             → isEquiv {A = Σ A B} {B = Σ A B'}
                       (λ (x , y) → (x , g x y))
pairEquiv2 g eg =
    let isog = (λ x → isEquiv→Iso (eg x)) 
    in Iso→isEquiv ( (λ (x , y) → (x , fst (isog x) y)) 
                   , ( (λ (x , y) → 
                          pairEq refl (fst (snd (isog x)) y)) 
                     , λ (x , y) → 
                         pairEq refl (snd (snd (isog x)) y)))

pairEquiv : ∀ {ℓ ℓ' κ κ'} {A : Type ℓ} {A' : Type ℓ'}
            → {B : A → Type κ} {B' : A' → Type κ'}
            → (f : A → A') (g : (x : A) → B x → B' (f x))
            → isEquiv f → ((x : A) → isEquiv (g x))
            → isEquiv {A = Σ A B} {B = Σ A' B'}
                      (λ (x , y) → (f x , g x y))
pairEquiv f g ef eg = 
    compIsEquiv (λ (x , y) → (f x , y)) 
                (λ (x , y) → (x , g x y)) 
                (pairEquiv1 f ef) 
                (pairEquiv2 g eg)


transpComp : ∀ {ℓ κ} {A : Type ℓ} {a b c : A} {B : A → Type κ}
             → (e1 : a ≡ b) (e2 : b ≡ c) (x : B a)
             → transp B e2 (transp B e1 x)
               ≡ transp B (a ≡〈 e1 〉 e2) x
transpComp refl refl x = refl

_•_ : ∀ {ℓ} {A : Type ℓ} {a b c : A}
      → (a ≡ b) → (b ≡ c) → (a ≡ c)
refl • refl = refl

comprewrite : ∀ {ℓ} {A : Type ℓ} {a b c : A}
              → (e1 : a ≡ b) (e2 : b ≡ c)
              → (a ≡〈 e1 〉 e2) ≡ (e1 • e2)
comprewrite refl refl = refl

{-# REWRITE comprewrite #-}

transpCompSymr : ∀ {ℓ κ} {A : Type ℓ} {a b : A} {B : A → Type κ}
                 → (e : a ≡ b) (x : B b)
                 → (transpComp (sym e) e x) • 
                     (ap (λ e' → transp B e' x) 
                         (sym (≡siml e)))
                   ≡ symr e x
transpCompSymr refl x = refl
```