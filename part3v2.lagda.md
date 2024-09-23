```agda
{-# OPTIONS --without-K --rewriting --lossy-unification #-}
module part3v2 where

open import part1v2
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import part2v2
open import appendixA
```

# Polynomials in HoTT

## Basics

**Remark:** for the sake of concision, since essentially all of the categorical structures treated in this paper will be infinite-dimensional, we shall generally omit the prefix "$\infty$-" from our descriptions these structures. Hence hereafter "category" generally means $\infty$-category, "functor" means $\infty$-functor, etc.

Let $\mathbf{Type}$ be the category of types and functions between them. Given a type `A`, let $y^A$ denote the corresponding representable functor $\mathbf{Type} \to \mathbf{Type}$.

A *polynomial functor* is a coproduct of representable functors $\mathbf{Type} \to \mathbf{Type}$, i.e. an endofunctor on $\mathbf{Type}$ of the form $$
\sum_{a : A} y^{B(a)}
$$ for some type `A` and family of types `B : A → Type`. The data of a polynomial functor is thus uniquely determined by the choice of `A` and `B`. Hence we may represent such functors in Agda simply as pairs (A , B) of this form:

```agda
Poly : (ℓ κ : Level) → Type ((lsuc ℓ) ⊔ (lsuc κ))
Poly ℓ κ = Σ (Type ℓ) (λ A → A → Type κ)
```

A basic example of such a polynomial functor is the identity functor `𝕪` consisting of a single term of unit arity – hence represented by the pair `(⊤ , λ _ → ⊤)`.

```agda
𝕪 : Poly lzero lzero
𝕪 = (⊤ , λ _ → ⊤)
```

The observant reader may note the striking similarity of the above-given formula for a polynomial functor and the endofunctor on $\mathbf{Set}^{\mathcal{C}^{op}}$ defined in the previous section on natural models. Indeed, this is no accident, given a type `𝓤` and a function `u : 𝓤 → Type` corresponding to a natural model as described previously, we obtain the corresponding polynomial `𝔲 : Poly` as the pair `(𝓤 , u)`. Hence we can study the structure of `𝓤` and `u` in terms of `𝔲`, and this, as we shall see, allows for some significant simplifications in the theory of natural models.

Given polynomial functors $p = \sum_{a : A} y^{B(a)}$ and $q = \sum_{c : C} y^{D(c)}$, a natural transformation $p \Rightarrow q$ is equivalently given by the data of a *forward* map `f : A → B` and a *backward* map `g : (a : A) → D (f a) → B a`, as can be seen from the following argument via Yoneda: $$
\begin{array}{rl}
& \int_{y \in \mathbf{Type}} \left( \sum_{a : A} y^{B(a)}  \right) \to \sum_{c : C} y^{D(c)}\\
\simeq & \prod_{a : A} \int_{y \in \mathbf{Type}} y^{B(a)} \to \sum_{c : C} y^{D(c)}\\
\simeq & \prod_{a : A} \sum_{c : C} B(a)^{D(c)}\\
\simeq & \sum_{f : A \to C} \prod_{a : A} B(a)^{D(f(c))}
\end{array}
$$ We use the notation $p \leftrightarrows q$ to denote the type of natural transformations from $p$ to $q$ (aka *lenses* from $p$ to $q$), which may be written in Agda as follows:

```agda
_⇆_ : ∀ {ℓ0 ℓ1 κ0 κ1} → Poly ℓ0 κ0 → Poly ℓ1 κ1 → Type (ℓ0 ⊔ ℓ1 ⊔ κ0 ⊔ κ1)
(A , B) ⇆ (C , D) = Σ (A → C) (λ f → (a : A) → D (f a) → B a)
```

By application of function extensionality, we derive the following type for proofs of equality between lenses: 

```agda
EqLens : ∀ {ℓ0 ℓ1 κ0 κ1}
         → {p : Poly ℓ0 κ0} (q : Poly ℓ1 κ1)
         → (f g : p ⇆ q) → Type (ℓ0 ⊔ ℓ1 ⊔ κ0 ⊔ κ1)
EqLens {p = (A , B)} (C , D) (f , f♯) (g , g♯) =
  Σ ((a : A) → f a ≡ g a)
    (λ e → (a : A) (d : D (f a)) 
           → f♯ a d ≡ g♯ a (transp D (e a) d))
```

For each polynomial $p$, the correspnding identity lens is given by the following data:

```agda
id : ∀ {ℓ κ} (p : Poly ℓ κ) → p ⇆ p
id p = ( (λ a → a) , λ a b → b )
```

And given lenses $p \leftrightarrows q$ and $q \leftrightarrows r$, their composition may be computed as follows:

```agda
comp : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
       → {p : Poly ℓ0 κ0} {q : Poly ℓ1 κ1} (r : Poly ℓ2 κ2)
       → p ⇆ q → q ⇆ r → p ⇆ r
comp r (f , f♯) (g , g♯) = 
     ( (λ a → g (f a)) , λ a z → f♯ a (g♯ (f a) z) )
```

Hence we have a category $\mathbf{Poly}$ of polynomial functors and lenses between them. Our goal, then, is to show how the type-theoretic structure of a natural model naturally arises from the structure of this category. In fact, $\mathbf{Poly}$ is replete with categorical structures of all kinds, of which we now mention but a few:

## The Vertical-Cartesian Factorization System on $\mathbf{Poly}$

We say that a lens `(f , f♯) : (A , B) ⇆ (C , D)` is *vertical* if `f : A → C` is an equivalence, and Cartesian if for every `a : A`, the map `f♯ a : D[f a] → B a` is an equivalence.

```agda
module Vert-Cart {ℓ0 ℓ1 κ0 κ1} {p : Poly ℓ0 κ0} 
                 (q : Poly ℓ1 κ1) (f : p ⇆ q) where

    isVertical : Set (ℓ0 ⊔ ℓ1)
    isVertical = isEquiv (fst f)

    isCartesian : Set (ℓ0 ⊔ κ0 ⊔ κ1)
    isCartesian = (a : fst p) → isEquiv (snd f a)

open Vert-Cart public
```

Every lens `(A , B) ⇆ (C , D)` can then be factored as a vertical lens followed by a Cartesian lens:

```agda
module VertCartFactor {ℓ0 ℓ1 κ0 κ1} {p : Poly ℓ0 κ0} 
                      (q : Poly ℓ1 κ1) (f : p ⇆ q) where

    vcIm : Poly ℓ0 κ1
    vcIm = (fst p , λ x → snd q (fst f x))

    vertfactor : p ⇆ vcIm
    vertfactor = ( (λ x → x) , (λ a x → snd f a x) )

    vertfactorIsVert : isVertical vcIm vertfactor
    vertfactorIsVert = idIsEquiv

    cartfactor : vcIm ⇆ q
    cartfactor = ( fst f , (λ a x → x) )

    cartfactorIsCart : isCartesian q cartfactor
    cartfactorIsCart x = idIsEquiv

    vertcartfactor≡ : EqLens q f (comp q vertfactor cartfactor)
    vertcartfactor≡ = ( (λ a → refl) , (λ a b → refl) )

open VertCartFactor public
```

Of these two classes of morphisms in $\mathbf{Poly}$, it is *Cartesian* lenses that shall be of principal interest to us. If we view a polynomial `p = (A , B)` as an `A`-indexed family of types, given by `B`, then given a lens `(f , f♯) : p ⇆ 𝔲`, we can think of the map `f♯ a : u (f a) → B a`, as an *elimination form* for the type `u (f a)`, i.e. a way of *using* elements of the type `u (f a)`. If we then ask that `(f , f♯)` isCartesian, this implies that the type `u (f a)` is completely characterized (up to equivalence) by this elimination form, and in this sense, `𝔲` *contains* the type `B a`, for all `a : A`.[^3]

[^3]: Those familiar with type theory may recognize this practice of defining types in terms of their elimination forms as characteristic of so-called *negative* types (in opposition to *positive* types, which are characterized by their introduction forms). Indeed, there are good reasons for this, having to do with the fact that negative types are equivalently those whose universal property is given by a *representable* functor, rather than a *co-representable* functor, which reflects the fact that natural models are defined in terms of *presheaves* on a category of contexts, rather than *co-presheaves.*

We can therefore use Cartesian lenses to detect which types are contained in a natural model `𝔲`.

A further fact about Cartesian lenses is that they are closed under identity and composition, as a direct consequence of the closure of equivalences under identity and composition:

```agda
idCart : ∀ {ℓ κ} (p : Poly ℓ κ)
         → isCartesian p (id p)
idCart p a = idIsEquiv

compCartesian : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
                → {p : Poly ℓ0 κ0} {q : Poly ℓ1 κ1} (r : Poly ℓ2 κ2)
                → {f : p ⇆ q} {g : q ⇆ r}
                → isCartesian q f → isCartesian r g 
                → isCartesian r (comp r f g)
compCartesian r {f = (f , f♯)} {g = (g , g♯)} cf cg a = 
    compIsEquiv (cf a) (cg (f a))
```

Hence there is a category $\mathbf{Poly^{Cart}}$ defined as the wide subcategory of $\mathbf{Poly}$ whose morphisms are precisely Cartesian lenses. As we shall see, much of the categorical structure of natural models qua polynomial functors can be derived from the subtle interplay between $\mathbf{Poly^{Cart}}$ and $\mathbf{Poly}$.

### Epi-Mono Factorization on $\mathbf{Poly^{Cart}}$

In fact, $\mathbf{Poly^{Cart}}$ itself inherits a factorization system from the epi-mono factorization on types considered previously.

Define a lens `(f , f♯) : p ⇆ q` to be a *vertical embedding* if `f` is a monomorphism, and a *vertical surjection* if `f` is an epimorphism.

```agda
module VertEpi-Mono {ℓ0 ℓ1 κ0 κ1} {p : Poly ℓ0 κ0} 
                    (q : Poly ℓ1 κ1) (f : p ⇆ q) where

    isVerticalEmbedding : Set (ℓ0 ⊔ ℓ1)
    isVerticalEmbedding = isMono (fst f)

    isVerticalSurjection : Set ℓ1
    isVerticalSurjection = isEpi (fst f)

open VertEpi-Mono public
```

Then every Cartesian lens can be factored into a vertical surjection followed by a vertical embedding, both of which are Cartesian.

```agda
module CartEMFactorization {ℓ0 ℓ1 κ0 κ1} {p : Poly ℓ0 κ0} 
           (q : Poly ℓ1 κ1) (f : p ⇆ q) (cf : isCartesian q f) where

    cartIm : Poly ℓ1 κ1
    cartIm = (Im (fst f) , λ (x , _) → snd q x)

    factorcart1 : p ⇆ cartIm
    factorcart1 = ( factor1 (fst f) , snd f )

    factorcart1IsCart : isCartesian cartIm factorcart1
    factorcart1IsCart = cf

    factorcart1IsEpi : isVerticalSurjection cartIm factorcart1
    factorcart1IsEpi = factor1IsEpi (fst f)

    factorcart2 : cartIm ⇆ q
    factorcart2 = ( factor2 (fst f) , (λ _ y → y) )

    factorcart2IsCart : isCartesian q factorcart2
    factorcart2IsCart _ = idIsEquiv

    factorcart2IsMono : isVerticalEmbedding q factorcart2
    factorcart2IsMono = factor2IsMono (fst f)

    factorcart≡ : EqLens q f (comp q factorcart1 factorcart2)
    factorcart≡ = ( (λ x →  refl) , (λ x y → refl) )

open CartEMFactorization public
```

We note in passing that the vertical embeddings are indeed the monomorphisms in $\mathbf{Poly}^{\mathbf{Cart}}$, i.e. if `f : q ⇆ r` is a both Cartesian and a vertical embedding, then for any Cartesian `g h : p ⇆ q` such that `f ∘ g ≡ f ∘ h`, we have `g = h`.[^1]

```agda
VertEmbedding→PolyCartMono : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2} {p : Poly ℓ0 κ0}
                             {q : Poly ℓ1 κ1} (r : Poly ℓ2 κ2) {f : q ⇆ r}
                             → isCartesian r f → isVerticalEmbedding r f
                             → {g h : p ⇆ q} → isCartesian q g → isCartesian q h
                             → EqLens r (comp r g f) (comp r h f)
                             → EqLens q g h
VertEmbedding→PolyCartMono {p = p} {q = q} r {f = (f , f♯)} cf vef 
                           {g = (g , g♯)} {h = (h , h♯)} cg ch (e , e♯) = 
    ( (λ a → inv vef (e a)) 
    , (λ a d → (g♯ a d) 
                   ≡〈 ap (g♯ a) (sym (snd (snd (cf (g a))) d)) 〉 
               ( _ ≡〈 (e♯ a (inv (cf (g a)) d)) 〉 
               ( _ ≡〈 (ap (h♯ a) 
                           ( _ ≡〈 (ap (f♯ (h a)) 
                                       (transpPre vef 
                                         (λ x y → inv (cf x) y) 
                                         (e a))) 〉 
                           ( _ ≡〈 snd (snd (cf (h a))) _ 〉 
                           ( _ □)))) 〉
               ((h♯ a (transp (snd q) (inv vef (e a)) d)) □)))) )
```

## Composition of Polynomial Functors

As endofunctors on $\mathbf{Type}$, polynomial functors may straightforwardly be composed. To show that the resulting composite is itself (equivalent to) a polynomial functor, we can reason via the following chain of equivalences: given polynomials `(A , B)` and `(C , D)`, their composite, evaluated at a type `y` is $$
\begin{array}{rl}
& \sum_{a : A} \prod_{b : B(a)} \sum_{c : C} y^{D(c)}\\
\simeq & \sum_{a : A} \sum_{f : B(a) \to C} \prod_{b : B(a)} y^{D(f(b))}\\
\simeq & \sum_{(a , f) : \sum_{a : A} C^{B(a)}} y^{\sum_{b : B(a)} D(f(b))}
\end{array}
$$ This then defines a monoidal product $◃$ on $\mathbf{Poly}$ with monoidal unit given by the identity functor `𝕪`:

```agda
_◃_ : ∀ {ℓ0 ℓ1 κ0 κ1} → Poly ℓ0 κ0 → Poly ℓ1 κ1 → Poly (ℓ0 ⊔ κ0 ⊔ ℓ1) (κ0 ⊔ κ1)
(A , B) ◃ (C , D) = (Σ A (λ a → B a → C) , λ (a , f) → Σ (B a) (λ b → D (f b)))

_◃◃[_]_ : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 κ0 κ1 κ2 κ3}
        → {p : Poly ℓ0 κ0} {q : Poly ℓ2 κ2} → p ⇆ q
        → {r : Poly ℓ1 κ1} (s : Poly ℓ3 κ3) → r ⇆ s 
        → (p ◃ r) ⇆ (q ◃ s)
(f , f♯) ◃◃[ s ] (g , g♯) =
    ((λ (a , γ) → (f a , λ b' → g (γ (f♯ a b'))))
    , λ (a , γ) (b' , d') → ((f♯ a b') , g♯ (γ (f♯ a b')) d'))

```

where `◃Lens` is the action of `◃` on lenses.

By construction, the existence of a Cartesian lens `(σ , σ♯) : 𝔲 ◃ 𝔲 ⇆ 𝔲` effectively shows that `𝔲` is closed under `Σ`-types, since:

* `σ` maps a pair (A , B) consisting of `A : 𝓤` and `B : (u A) → 𝓤` to a term `σ(A,B)` representing the `Σ` type. This corresponds to the type formation rule $$ \inferrule{\Gamma \vdash A : \mathsf{Type}\\ \Gamma, x : A \vdash B[x] ~ \mathsf{Type}}{\Gamma \vdash \Sigma x : A . B[x] ~ \mathsf{Type}} $$
* For all `(A , B)` as above, `σ♯ (A , B)` takes a term of type `σ (A , B)` and yields a term `fst (σ♯ (A , B)) : A` along with a term `snd (σ♯ (A , B)) : B (fst (σ♯ (A , B)))`, corresponding to the elimination rules $$
\inferrule{\Gamma \vdash p : \Sigma x : A . B[x]}{\Gamma \vdash \pi_1(p) : A} \quad \inferrule{\Gamma \vdash p : \Sigma x : A . B[x]}{\Gamma \vdash \pi_2(p) : B[\pi_1(p)]} $$
* The fact that `σ♯ (A , B)` has is an equivalence implies it has an inverse `σ♯⁻¹ (A , B) : Σ (u A) (λ x → u (B x)) → u (σ (A , B))`, which takes a pair of terms to a term of the corresponding pair type, and thus corresponds to the introduction rule $$ \inferrule{\Gamma \vdash a : A\\ \Gamma \vdash b : B[a]}{\Gamma \vdash (a , b) : \Sigma x : A . B[x]} $$
* The fact that $σ♯⁻¹ (A , B)$ is both a left and a right inverse to $σ♯$ then implies the usual $β$ and $η$ laws for dependent pair types $$ \pi_1(a , b) = a \quad \pi_2(a , b) = b \quad p = (\pi_1(p) , \pi_2(p)) $$

Similarly, the existence of a Cartesian lens $(η , η♯) : 𝕪 ⇆ 𝔲$ implies that $𝔲$ contains (a type equivalent to) the unit type, in that:

* There is an element `η tt : 𝓤` which represents the unit type. This corresponds to the type formation rule $$ \inferrule{~}{\Gamma \vdash \top : \mathsf{Type}}$$
* The "elimination rule" `η♯ tt : u(η tt) → ⊤`, applied to an element `x : u(η tt)` is trivial, in that it simply discards `x`. This corresponds to the fact that, in the ordinary type-theoretic presentation, $\top$ does not have an elimination rule.
* However, since this trivial elimination rule has an inverse `η♯⁻¹ tt : ⊤ → u (η tt)`, it follows that there is a (unique) element `η♯⁻¹ tt tt : u (η tt)`, which corresponds to the introduction rule for $\top$: $$\inferrule{~}{\Gamma \vdash \mathsf{tt} : \top}$$
* Moreover, the uniqueness of this element corresponds to the $\eta$-law for $\top$: $$\frac{\Gamma \vdash x : \top}{\Gamma \vdash x = \mathsf{tt}}$$

But then, what sorts of laws can we expect Cartesian lenses as above to obey, and is the existence of such a lens all that is needed to ensure that the natural model $𝔲$ has dependent pair types in the original sense of Awodey & Newstead's definition in terms of Cartesian (pseudo)monads, or is some further data required? And what about `Π` types, or other type formers? To answer these questions, we will need to study the structure of `◃`, along with some closely related functors, in a bit more detail. In particular, we shall see that the structure of `◃` as a monoidal product on $\mathbf{Poly}$ reflects many of the basic identities one expects to hold of `Σ` types.

For instance, the associativity of `◃` corresponds to the associativity of `Σ`-types.

```agda
module ◃Assoc {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2} (p : Poly ℓ0 κ0) 
              (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2) where

    ◃assoc : ((p ◃ q) ◃ r) ⇆ (p ◃ (q ◃ r))
    ◃assoc = ( (λ ((a , γ) , δ) 
                  → (a , (λ b → (γ b , λ d → δ (b , d))))) 
             , (λ _ (b , (d , x)) → ((b , d) , x)) )
    
    ◃assoc⁻¹ : (p ◃ (q ◃ r)) ⇆ ((p ◃ q) ◃ r)
    ◃assoc⁻¹ = ( (λ (a , γ) → ( (a , (λ x → fst (γ x))) 
                              , (λ (x , y) → snd (γ x) y) ))
               , λ _ ((x , y) , z) → (x , (y , z)) )

open ◃Assoc public
```

while the left and right unitors of `◃` correspond to the fact that `⊤` is both a left and a right unit for `Σ`-types.

```agda
module ◃LRUnit {ℓ κ} (p : Poly ℓ κ) where

    ◃unitl : (𝕪 ◃ p) ⇆ p
    ◃unitl = ( (λ (_ , a) → a tt) , λ (_ , a) x → (tt , x) )

    ◃unitl⁻¹ : p ⇆ (𝕪 ◃ p)
    ◃unitl⁻¹ = ( (λ a → (tt , λ _ → a)) , (λ a (_ , b) → b ) )

    ◃unitr : (p ◃ 𝕪) ⇆ p
    ◃unitr = ( (λ (a , γ) → a) , (λ (a , γ) b → (b , tt)) )

    ◃unitr⁻¹ : p ⇆ (p ◃ 𝕪)
    ◃unitr⁻¹ = ( (λ a → a , (λ _ → tt)) , (λ a (b , _) → b) )

open ◃LRUnit public
```

n fact, `◃` restricts to a monoidal product on $\mathbf{Poly^{Cart}}$, since the functorial action of `◃` on lenses preserves Cartesian lenses,

```agda
◃◃Cart : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 κ0 κ1 κ2 κ3}
         → {p : Poly ℓ0 κ0} (q : Poly ℓ2 κ2) {f : p ⇆ q}
         → {r : Poly ℓ1 κ1} (s : Poly ℓ3 κ3) {g : r ⇆ s}
         → isCartesian q f → isCartesian s g
         → isCartesian (q ◃ s) (f ◃◃[ s ] g)
◃◃Cart q {f = (f , f♯)} s {g = (g , g♯)} cf cg (a , γ) = 
    pairEquiv (f♯ a) (λ x → g♯ (γ (f♯ a x))) 
              (cf a) (λ x → cg (γ (f♯ a x)))
```

and all of the above-defined structure morphisms for `◃` are Cartesian.

```agda
module ◃AssocCart {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2} (p : Poly ℓ0 κ0) 
                  (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2) where

    ◃assocCart : isCartesian (p ◃ (q ◃ r)) (◃assoc p q r)
    ◃assocCart _ = 
        Iso→isEquiv (snd (◃assoc⁻¹ p q r) _ , ((λ _ → refl) , (λ _ → refl)))
    
    ◃assoc⁻¹Cart : isCartesian ((p ◃ q) ◃ r) (◃assoc⁻¹ p q r)
    ◃assoc⁻¹Cart _ = 
        Iso→isEquiv (snd (◃assoc p q r) _ , ((λ _ → refl) , (λ _ → refl)))

open ◃AssocCart public

module ◃LRUnitCart {ℓ κ} (p : Poly ℓ κ) where

    ◃unitlCart : isCartesian p (◃unitl p)
    ◃unitlCart _ = Iso→isEquiv (snd (◃unitl⁻¹ p) _ , ((λ _ → refl) , (λ _ → refl)))

    ◃unitl⁻¹Cart : isCartesian (𝕪 ◃ p) (◃unitl⁻¹ p)
    ◃unitl⁻¹Cart _ = Iso→isEquiv (snd (◃unitl p) _ , ((λ _ → refl) , (λ _ → refl)))

    ◃unitrCart : isCartesian p (◃unitr p)
    ◃unitrCart _ = Iso→isEquiv (snd (◃unitr⁻¹ p) _ , ((λ _ → refl) , (λ _ → refl)))

    ◃unitr⁻¹Cart : isCartesian (p ◃ 𝕪) (◃unitr⁻¹ p)
    ◃unitr⁻¹Cart _ = Iso→isEquiv (snd (◃unitr p) _ , ((λ _ → refl) , (λ _ → refl)))

open ◃LRUnitCart public
```

We should expect, then, for these equivalences to be somehow reflected in the structure of a Cartesian lenses `η : 𝕪 ⇆ 𝔲` and `μ : 𝔲 ◃ 𝔲 ⇆ 𝔲`. This would be the case, e.g., if the following diagrams in $\mathbf{Poly^{Cart}}$ were to commute $$
\begin{tikzcd}
	{y \triangleleft \mathfrak{u}} & {\mathfrak{u} \triangleleft \mathfrak{u} } & {\mathfrak{u} \triangleleft y} \\
	& {\mathfrak{u}}
	\arrow["{\eta \triangleleft \mathfrak{u}}", from=1-1, to=1-2]
	\arrow["{\mathsf{\triangleleft unitl}}"{description}, from=1-1, to=2-2]
	\arrow["\mu", from=1-2, to=2-2]
	\arrow["{\mathfrak{u} \triangleleft \eta}"', from=1-3, to=1-2]
	\arrow["{\mathsf{\triangleleft unitr}}"{description}, from=1-3, to=2-2]
\end{tikzcd} \qquad \begin{tikzcd}
	{(\mathfrak{u} \triangleleft \mathfrak{u}) \triangleleft \mathfrak{u}} & {\mathfrak{u} \triangleleft (\mathfrak{u} \triangleleft \mathfrak{u})} & {\mathfrak{u} \triangleleft \mathfrak{u}} \\
	{\mathfrak{u} \triangleleft \mathfrak{u}} && {\mathfrak{u}}
	\arrow["{\mathsf{\triangleleft assoc}}", from=1-1, to=1-2]
	\arrow["{\mu \triangleleft \mathfrak{u}}"', from=1-1, to=2-1]
	\arrow["{\mathfrak{u} \triangleleft \mu}", from=1-2, to=1-3]
	\arrow["\mu", from=1-3, to=2-3]
	\arrow["\mu"', from=2-1, to=2-3]
\end{tikzcd}
$$

One may recognize these as the usual diagrams for a monoid in a monoidal category, hence (since `◃` corresponds to composition of polynomial endofunctors) for a *monad* as typically defined. However, because of the higher-categorical structure of types in HoTT, we should not only ask for these diagrams to commute, but for the cells exhibiting that these diagrams commute to themselves be subject to higher coherences, and so on, giving `𝔲` not the structure of a (Cartesian) monad, but rather of a (Cartesian) *$\infty$-monad*.

Yet demonstrating that $𝔲$ is an $\infty$-monad involves specifying a potentially infinite amount of coherence data. Have we therefore traded both the Scylla of equality-up-to-isomorphism and the Charybdis of strictness for an even worse fate of higher coherence hell? The answer to this question, surprisingly, is negative, as there is a way to implicitly derive all of this data from a single axiom, which corresponds to the characteristic axiom of HoTT itself: univalence. To show this, we now introduce the central concept of this paper – that of a *polynomial universe*. 