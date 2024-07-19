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

Awodey, later with Newstead, showed how polynomial pseudomonads $(u,\1,\Sigma)$ with extra structure (termed "natural models" by Awodey) hold within them the syntax and rules for dependent type theory. Their work presented these ideas clearly but ultimately led them outside of the category of polynomial functors in order to explicate all of the structure possessed by such models of type theory.

This paper builds off that work---explicating the syntax and rules for dependent type theory by axiomatizing them \emph{entirely} in the language of polynomial functors. In order to handle the higher-categorical coherences required by such an explication, we work with polynomial functors internally in the language of Homotopy Type Theory, which allows for higher-dimensional structures such as pseudomonads, etc. to be expressed purely in terms of the structure of a suitably-chosen $(2,1)$-category of polynomial functors. The move from set theory to Homotopy Type Theory thus has a twofold effect of enabling a simpler exposition of natural models, which is at the same time amenable to formalization in a proof assistant, such as Agda.

Moreover, the choice to remain firmly within the setting of polynomial functors reveals many additional structures of natural models that were otherwise left implicit or not considered by Awodey \& Newstead. Chief among these, we highlight the fact that every polynomial pseudomonad $(u,\1,\Sigma)$ as above that is also equipped with structure to interpret dependent product types gives rise to a self-distributive law $u\tri u\to u\tri u$, which witnesses the usual distributive law of dependent products over dependent sums.
\end{abstract}

# Introduction

Dependent type theory \cite{martin-lof1975intuitionistic} was founded by Per Martin-Löf in 1975 to formalize constructive mathematics. The basic idea is that the \emph{order of events} is fundamental to the mathematical story arc: when playing out any specific example story in that arc, the beginning of the story affects not only the later events, but even the very terms with which the later events will be described. For example, in the story arc of conditional probability, one may say ``now if the set $P$ that we are asked to condition on happens to have measure zero, we must stop; but assuming that's not the case then the result will be a new probability measure.'' Here the story teller is saying that no terms will describe what happens if $P$ has measure zero, whereas otherwise the terms of standard probability will apply.

Dependent types form a logical system with syntax, rules of computation, and methods of deduction. In \cite{awodey2014natural,awodey2018polynomial}, Awodey and later Newstead show that there is a strong connection between dependent type theory and polynomial functors, via their concept of *natural models*, which cleanly solve the problem of *strictififying* certain identities that typically hold only up to isomorphism in arbitrary categories, but must hold *strictly* in order for these to soundly model dependent type theory. The solution to this problem offered by Awodey and Newstead makes use of the type-theoretic concept of a *universe*. Such universes then turn out to naturally be regarded as polynomial functors on a suitably-chosen category of presheaves, satisfying a certain *representability* condition.

Although the elementary structure of natural models is thus straightforwardly described by considering them as objects in the category of polynomial functors, Awodey and Newstead were ultimately led outside of this category in order to fully explicate those parts of natural models that require identities to hold only *up to isomorphism*, rather than strictly. There is thus an evident tension between *strict* and *weak* identities that has not yet been fully resolved in the story of natural models. In the present work, we build on Awodey and Newstead's work to fully resolve this impasse by showing how type universes can be fully axiomatized in terms of polynomial functors, by working with polynomial functors internally in the language of *Homotopy Type Theory* (HoTT). We thus come full circle from Awodey's original motivation to develop natural models *of* Homotopy Type Theory, to describing natural models *in* Homotopy Type Theory.

The ability for us to tell the story of natural models as set entirely in the category of polynomial functors has a great simplifying effect upon the resultant theory, and reveals many additional structures, both of polynomial universes, and of the category of polynomial functors as a whole. As an illustration of this, we show how every polynomial universe, regarded as a polynomial pseudomonad with additional structure, gives rise to self-distributive law $u\tri u\to u\tri u$, which witnesses the usual distributive law of dependent products over dependent sums.

Moreover, the move from set theory to HoTT as a setting in which to tell this story enables new tools to be applied for its telling. In particular, the account of polynomial universes we develop is well-suited to formalization in a proof assistant, and we present such a formalization in Agda. This paper is thus itself a literate Agda document in which all results have been fully formalized and checked for validity.

```agda
{-# OPTIONS --without-K --rewriting #-}
module poly-universes where

open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
```

The structure of this paper is as follows:

# Background on HoTT and Polynomial Functors

We begin with a quick recap of the basics of HoTT and polynomial functors.

## Homotopy Type Theory

```agda
Type : (ℓ : Level) → Set (lsuc ℓ)
Type ℓ = Set ℓ
```

```agda
isContr : ∀ {ℓ} → Type ℓ → Type ℓ
isContr A = Σ A (λ a → (b : A) → a ≡ b)

isProp : ∀ {ℓ} → Type ℓ → Type ℓ
isProp A = (a b : A) → a ≡ b

isSet : ∀ {ℓ} → Type ℓ → Type ℓ
isSet A = (a b : A) → isProp (a ≡ b)

isGrpd : ∀ {ℓ} → Type ℓ → Type ℓ
isGrpd A = (a b : A) → isSet (a ≡ b)

isEquiv : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ}
          → (A → B) → Set (ℓ ⊔ κ)
isEquiv {A = A} {B = B} f = (b : B) → isContr (Σ A (λ a → f a ≡ b))

inv : ∀ {ℓ κ} {A : Type ℓ} {B : Type κ} {f : A → B}
      → isEquiv f → B → A
inv e b = fst (fst (e b))

ap : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
     → f ≡ g → (x : A) → f x ≡ g x
ap refl x = refl

postulate
    funext1 : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
              → ((x : A) → f x ≡ g x) → f ≡ g
    funext2 : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f : (x : A) → B x}
              → funext1 {f = f} {g = f} (λ x → refl) ≡ refl
    {-# REWRITE funext2 #-}
```

## Polynomials in HoTT

```agda
Poly : (ℓ κ : Level) → Type ((lsuc ℓ) ⊔ (lsuc κ))
Poly ℓ κ = Σ (Set ℓ) (λ A → A → Set κ)
```

```agda
_⇆_ : ∀ {ℓ ℓ' κ κ'} → Poly ℓ κ → Poly ℓ' κ' → Type (ℓ ⊔ ℓ' ⊔ κ ⊔ κ')
(A , B) ⇆ (C , D) = 
    Σ (A → C) 
      (λ f → (a : A) → D (f a) → B a)
```

```agda
id : ∀ {ℓ κ} {p : Poly ℓ κ} → p ⇆ p
id = ( (λ a → a) 
     , λ a b → b)

_∘_ : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
      → {p : Poly ℓ κ} {q : Poly ℓ' κ'} {r : Poly ℓ'' κ''}
      → q ⇆ r → p ⇆ q → p ⇆ r
(h , k) ∘ (f , g) = 
    ( (λ a → h (f a)) 
    , λ a z → g a (k (f a) z))

infixr 10 _∘_
```

record Poly {ℓ κ} : Type ((lsuc ℓ) ⊔ (lsuc κ)) where
    constructor poly
    field
        Pos : Type ℓ
        Dir : Pos → Type κ
        posIsGrpd : isGrpd Pos
        dirIsSet : (p : Pos) → isSet (Dir p)


### Basics

### Univalence

```agda
idToEquiv : ∀ {ℓ κ} (p : Poly ℓ κ) (a b : fst p)
            → a ≡ b → Σ (snd p a → snd p b) isEquiv
idToEquiv p a b refl = (λ x → x) , (λ y → (y , refl) , (λ { (y' , refl) → refl }))

isUnivalent : ∀ {ℓ κ} → Poly ℓ κ → Type (ℓ ⊔ κ)
isUnivalent (A , B) = 
    (a b : A) → isEquiv (idToEquiv (A , B) a b)
```

### The Vertical-Cartesian Factorization System

```agda
isVertical : ∀ {ℓ ℓ' κ κ'} {p : Poly ℓ κ} {q : Poly ℓ' κ'}
             → p ⇆ q → Set (ℓ ⊔ ℓ')
isVertical (f , g) = isEquiv f

isCartesian : ∀ {ℓ ℓ' κ κ'} {p : Poly ℓ κ} {q : Poly ℓ' κ'}
             → p ⇆ q → Set (ℓ ⊔ κ ⊔ κ')
isCartesian {p = (A , B)} (f , g) = (a : A) → isEquiv (g a)
```

### The Composition and Dirichlet Monoidal Products

```agda
𝐲 : Poly lzero lzero
𝐲 = ⊤ , λ _ → ⊤

_◃_ : ∀ {ℓ ℓ' κ κ'} → Poly ℓ κ → Poly ℓ' κ' → Poly (ℓ ⊔ κ ⊔ ℓ') (κ ⊔ κ')
(A , B) ◃ (C , D) = (Σ A (λ a → B a → C) , λ (a , f) → Σ (B a) (λ b → D (f b)))

_◃◃_ : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
       → {p : Poly ℓ κ} {p' : Poly ℓ' κ'} {q : Poly ℓ'' κ''} {q' : Poly ℓ''' κ'''}
       → p ⇆ p' → q ⇆ q' → (p ◃ q) ⇆ (p' ◃ q')
(f , g) ◃◃ (h , k) = 
    ((λ (a , c) → (f a , λ b' → h (c (g a b'))))
    , λ (a , c) (b' , d') → ((g a b') , k (c (g a b')) d'))

◃assoc : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
         → {p : Poly ℓ κ} {q : Poly ℓ' κ'} {r : Poly ℓ'' κ''}
         → ((p ◃ q) ◃ r) ⇆ (p ◃ (q ◃ r))
◃assoc = 
    ((λ ((a , f) , g) → (a , (λ b → (f b , λ d → g (b , d))))) 
    , λ ((a , f) , g) (b , (d , x)) → ((b , d) , x))

◃assocVert : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
             → {p : Poly ℓ κ} {q : Poly ℓ' κ'} {r : Poly ℓ'' κ''}
             → isVertical {p = ((p ◃ q) ◃ r)} 
                          {q = (p ◃ (q ◃ r))} 
                          (◃assoc {p = p} {q = q} {r = r})
◃assocVert (a , f) = 
    ( ( ( (a , (λ b → fst (f b))) 
        , λ (b , d) → snd (f b) d) 
      , refl)
    , λ { (x , refl) → refl })

◃assocCart : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
             → {p : Poly ℓ κ} {q : Poly ℓ' κ'} {r : Poly ℓ'' κ''}
             → isCartesian {p = ((p ◃ q) ◃ r)} 
                           {q = (p ◃ (q ◃ r))} 
                           (◃assoc {p = p} {q = q} {r = r})
◃assocCart (a , f) ((b , d) , x) = 
    ( ((b , (d , x)) , refl)
    , λ { (x , refl) → refl })

_⊗_ : ∀ {ℓ ℓ' κ κ'} → Poly ℓ κ → Poly ℓ' κ' → Poly (ℓ ⊔ ℓ') (κ ⊔ κ')
(A , B) ⊗ (C , D) = (Σ A (λ _ → C) , λ (a , c) → Σ (B a) (λ _ → D c))
```

### The $\upuparrows$ and $(-)^=$ Functors

```agda
_⇈_ : ∀ {ℓ ℓ' κ κ'} → Poly ℓ κ → Poly ℓ' κ' → Poly (ℓ ⊔ κ ⊔ ℓ') (κ ⊔ κ')
(A , B) ⇈ (C , D) = (Σ A (λ a → B a → C) , λ (a , f) → (b : B a) → D (f b))

_⁼ : ∀ {ℓ κ} → Poly ℓ κ → Poly (ℓ ⊔ κ) κ
(A , B)⁼ = (Σ A (λ a → Σ (B a) (λ _ → B a)) , λ (a , b , b') → b ≡ b')
```

```agda
⇈curry : ∀ {ℓ ℓ' ℓ'' κ κ' κ''} 
         → {p : Poly ℓ κ} {q : Poly ℓ' κ'} {r : Poly ℓ'' κ''}
         → ((p ◃ q) ⇈ r) ⇆ (p ⇈ (q ⇈ r))
⇈curry = 
    ((λ ((a , f) , g) → 
        (a , (λ b → (f b , λ d → g (b , d))))) 
    , λ ((a , f) , g) h → λ (b , d) → h b d)

⇈curryIsCartesian : ∀ {ℓ ℓ' ℓ'' κ κ' κ''} 
                    → {p : Poly ℓ κ} {q : Poly ℓ' κ'} {r : Poly ℓ'' κ''}
                    → isCartesian {p = ((p ◃ q) ⇈ r)} 
                                  {q = (p ⇈ (q ⇈ r))} 
                                  (⇈curry {p = p} {q = q} {r = r})
⇈curryIsCartesian ((a , f) , g) h = 
    ( ((λ b d → h (b , d)) , refl) 
    , λ {(h' , refl) → refl})

⇈distribute : ∀ {ℓ ℓ' ℓ'' κ κ' κ''} 
              → {p : Poly ℓ κ} {q : Poly ℓ' κ'} {r : Poly ℓ'' κ''}
              → (p ⇈ (q ◃ r)) ⇆ ((p ⇈ q) ◃ (p ⇈ r))
⇈distribute = 
    ( (λ (a , f) → ((a , (λ b → fst (f b))) 
      , λ g → (a , λ b → snd (f b) (g b))))
    , λ (a , f) (g , h) b → (g b , h b))

⇈distributeIsCartesian : ∀ {ℓ ℓ' ℓ'' κ κ' κ''} 
                        → {p : Poly ℓ κ} {q : Poly ℓ' κ'} {r : Poly ℓ'' κ''}
                         → isCartesian {p = (p ⇈ (q ◃ r))} 
                                       {q = ((p ⇈ q) ◃ (p ⇈ r))} 
                                       (⇈distribute {p = p} {q = q} {r = r})
⇈distributeIsCartesian (a , f) g = 
    ( (((λ b → fst (g b)) , λ b → snd (g b)) , refl)
    , λ { ((g' , h') , refl) → refl })
```

```agda
app : ∀ {ℓ ℓ' κ κ'} {p : Poly ℓ κ} {q : Poly ℓ' κ'}
      → (p ◃ q) ⇆ ((p ⇈ q) ⊗ p)
app = 
    (λ (a , f) → ((a , f) , a)) 
    , λ (a , f) (g , b) → (b , g b)
```

# Polynomial Universes \& Jump Monads

## Polynomial Universes

```agda
record Universe (ℓ κ : Level) : Type ((lsuc ℓ) ⊔ (lsuc κ)) where
    field
        UPoly : Poly ℓ κ
        UUniv : isUnivalent UPoly
        U⊤ : 𝐲 ⇆ UPoly
        U⊤Cart : isCartesian {p = 𝐲} {q = UPoly} U⊤
        UΣ : (UPoly ◃ UPoly) ⇆ UPoly
        UΣCart : isCartesian {p = (UPoly ◃ UPoly)} {q = UPoly} UΣ
        UΠ : (UPoly ⇈ UPoly) ⇆ UPoly
        UΠCart : isCartesian {p = (UPoly ⇈ UPoly)} {q = UPoly} UΠ
open Universe
```

```agda
{- UΣassoc : ∀ {ℓ κ} {u : Universe ℓ κ}
          → (UΣ u) ∘ ((UΣ u) ◃◃ id) ≡ (UΣ u) ∘ (id ◃◃ (UΣ u)) ∘ ◃assoc
UΣassoc = refl -}
```

## Jump Monads \& Distributive Laws  