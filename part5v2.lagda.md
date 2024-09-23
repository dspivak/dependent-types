```agda
{-# OPTIONS --without-K --rewriting #-}
module part5v2 where

open import part1v2
open import Agda.Primitive
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import part2v2
open import appendixA
open import part3v2
open import part4v2
```

# $\Pi$-Types & Distributive Laws

We have so far considered how polynomial universes may be equipped with structure to interpret the unit type and dependent pair types. We have not yet, however, said much in the way of *dependent function types.* In order to rectify this omission, it will first be prudent to consider some additional structure on the category of polynomial functors – specifically a new functor ${\upuparrows}[\_] : \mathsf{Tw}(\mathbf{Poly}) \times \mathbf{Poly} \to \mathbf{Poly}$ that plays a similar role for `Π` types as the composition $\triangleleft : \mathbf{Poly} \times \mathbf{Poly} \to \mathbf{Poly}$ played for `Σ` types, and which in turn bears a close connection to *distributive laws* in $\mathbf{Poly}$.

## The $\upuparrows$ and ${\upuparrows}[\_]$ Functors

The $\upuparrows$ functor can be loosely defined as the solution to the following problem: given a polynomial universe `𝔲`, find `𝔲 ⇈ 𝔲` such that `𝔲` classifies `𝔲 ⇈ 𝔲` if and only if `𝔲` has the structure to interpret `Π` types (in the same way that `𝔲` classifies `𝔲 ◃ 𝔲` if and only if `𝔲` has the structure to interpret `Σ` types). Generalizing this to arbitrary pairs of polynomials $p = (A , B), ~ q = (C , D)$ then yields the following formula for $p \upuparrows q$: $$
p \upuparrows q = \sum_{(a , f) : \sum_{a : A} C^{B(a)}} y^{\prod_{b : B(a)} D(f(b))}
$$

```agda
_⇈_ : ∀ {ℓ0 ℓ1 κ0 κ1} → Poly ℓ0 κ0 → Poly ℓ1 κ1 
      → Poly (ℓ0 ⊔ κ0 ⊔ ℓ1) (κ0 ⊔ κ1)
(A , B) ⇈ (C , D) = 
    ( Σ A (λ a → B a → C) 
    , (λ (a , f) → (b : B a) → D (f b)))
```

Note that this construction is straightforwardly functorial with respect to arbitrary lenses in its 2nd argument. Functoriality of the 1st argument is trickier, however. For reasons that will become apparent momentarily, we define the functorial action $p \upuparrows q \leftrightarrows p' \upuparrows q$ of $\upuparrows$ on a lens $f : p \leftrightarrows p'$ equipped with a left inverse $f' : p' \leftrightarrows p$, i.e. such that $f' \circ f = \text{id}_p$.

```agda
⇈Lens : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 κ0 κ1 κ2 κ3}
        → {p : Poly ℓ0 κ0} (r : Poly ℓ2 κ2)
        → {q : Poly ℓ1 κ1} (s : Poly ℓ3 κ3)
        → (f : p ⇆ r) (f' : r ⇆ p) 
        → EqLens p (id p) (comp p f f')
        → (g : q ⇆ s) → (p ⇈ q) ⇆ (r ⇈ s)
⇈Lens {p = p} r s (f , f♯) (f' , f'♯) (e , e♯) (g , g♯) = 
    ( (λ (a , γ) → (f a , (λ x → g (γ (f♯ a x)))))
    , (λ (a , γ) Ϝ x → 
         g♯ (γ x) 
            (transp (λ y → snd s (g (γ y))) 
                    (sym (e♯ a x)) 
                    (Ϝ (f'♯ (f a) (transp (snd p) (e a) x))))) )
```

By construction, the existence of a Cartesian lens `(π , π♯) : 𝔲 ◃ 𝔲 ⇆ 𝔲` effectively shows that `𝔲` is closed under `Π`-types, since:

* `π` maps a pair `(A , B)` consisting of `A : 𝓤` and `B : u(A) → 𝓤` to a term `π(A,B)` representing the corresponding `Π` type. This corresponds to the type formation rule $$ \inferrule{\Gamma \vdash A : \mathsf{Type}\\ \Gamma, x : A \vdash B[x] ~ \mathsf{Type}}{\Gamma \vdash \Pi x : A . B[x] ~ \mathsf{Type}} $$
* The "elimination rule" `π♯ (A , B)`, for any pair `(A , B)` as above, maps an element `f : π(A,B)` to a function `π♯ (A , B) f : (a : u(A)) → u (B x)` which takes an element `x` of `A` and yields an element of `B x`. This corresponds to the rule for function application: $$
\inferrule{\Gamma \vdash f : \Pi x : A . B[x]\\ \Gamma \vdash a : A}{\Gamma \vdash f ~ a : B[a]}
$$
* Since `π♯ (A , B)` is an equivalence, it follows that there is an inverse `π♯⁻¹ (A , B) : ((x : u(A)) → u(B(x)) → u(π(A,B))`, which corresponds to $\lambda$-abstraction: $$
\inferrule{\Gamma, x : A \vdash f[x] : B[x]}{\Gamma \vdash \lambda x . f[x] : \Pi x : A . B[x]}
$$
* The fact that `π♯⁻¹ (A , B)` is both a left and a right inverse to `π♯` then corresponds to the $\beta$ and $\eta$ laws for `Π` types. $$
(\lambda x . f[x]) ~ a = f[a] \qquad f = \lambda x . f ~ x
$$

Although it is clear enough that the $\upuparrows$ functor serves its intended purpose of characterizing `Π` types in polynomial universes, its construction seems somewhat more ad hoc than that of $\triangleleft$, which similarly characterized `Σ` types in polynomial universes while arising quite naturally from composition of polynomial functors. We would like to better understand what additional properties $\upuparrows$ must satisfy, and how these in turn are reflected as properties of polynomial universes with `Π` types. In fact, we will ultimately show that this construction is intimately linked with a quite simple structure on polynomial universes `𝔲`, namely a *distributive law* of `𝔲` (viewed as a monad) over itself. Before that, however, we note some other key properties of $\upuparrows$.

Specifically, let $\mathbf{Poly}_{R}$ be the wide subcategory of $\mathbf{Poly}$ spanned by morphisms equipped with left inverses. Straightforwardly, $\triangleleft$ restricts to a monoidal product on $\mathbf{Poly}_R$, since it is functorial in both arguments and must preserve left/right inverses. Hence $\upuparrows$ can be viewed as a functor $\mathbf{Poly}_R \times \mathbf{Poly} \to \mathbf{Poly}$. Then $\upuparrows$ moreover naturally carries the structure of an *action* on $\mathbf{Poly}$ of the monoidal category $\mathbf{Poly}_R$ equipped with $\triangleleft$, in that there are natural transformations $$
\mathbb{y} \upuparrows p \to p $$ $$
(p \triangleleft q) \upuparrows r \to p \upuparrows (q \upuparrows r)
$$ which are moreover *Cartesian*:

```agda
module Unit⇈ {ℓ κ} (p : Poly ℓ κ) where

    𝕪⇈ : (𝕪 ⇈ p) ⇆ p
    𝕪⇈ = ( (λ (_ , a) → a tt) , λ (_ , a) b tt → b)

    𝕪⇈Cart : isCartesian p 𝕪⇈
    𝕪⇈Cart (_ , x) = 
        Iso→isEquiv ( (λ Ϝ → Ϝ tt) 
                    , ( (λ a → refl) 
                      , λ b → refl))

open Unit⇈ public

module ◃⇈ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2} (p : Poly ℓ0 κ0) 
          (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2) where

    ⇈Curry : ((p ◃ q) ⇈ r) ⇆ (p ⇈ (q ⇈ r))
    ⇈Curry = ( (λ ((a , h) , k) 
                  → (a , (λ b → ( (h b) 
                                , (λ d → k (b , d))))))
             , (λ ((a , h) , k) f (b , d) → f b d) )
    
    ⇈CurryCart : isCartesian (p ⇈ (q ⇈ r)) ⇈Curry
    ⇈CurryCart ((a , h) , k) = 
        Iso→isEquiv ( (λ f b d → f (b , d)) 
                    , ( (λ f → refl)
                      , (λ f → refl) ) )

open ◃⇈ public
```

The fact that `⇈Curry` is Cartesian corresponds to the usual currying isomorphism that relating dependent functions types to dependent pair types: $$
\Pi (x , y) : \Sigma x : A . B[x] . C[x,y] \simeq \Pi x : A . \Pi y : B[x] . C[x,y]
$$

Similarly, $\upuparrows$ is colax with respect to $\triangleleft$ in its second argument, in that there are Cartesian natural transformations $$
p \upuparrows \mathbb{y} → \mathbb{y}
$$ $$
p \upuparrows (q \triangleleft r) \to (p \upuparrows q) \triangleleft (p \upuparrows r)
$$

```agda
module ⇈Unit {ℓ κ} (p : Poly ℓ κ) where

    ⇈𝕪 : (p ⇈ 𝕪) ⇆ 𝕪
    ⇈𝕪 = ( (λ (a , γ) → tt) , λ (a , γ) tt b → tt )

    ⇈𝕪Cart : isCartesian 𝕪 ⇈𝕪
    ⇈𝕪Cart (x , γ) = 
        Iso→isEquiv ( (λ x → tt) 
                    , ( (λ a → refl) 
                      , λ b → refl))

open ⇈Unit public

module ⇈◃ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2} (p : Poly ℓ0 κ0) 
          (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2) where

    ⇈Distr : (p ⇈ (q ◃ r)) ⇆ ((p ⇈ q) ◃ (p ⇈ r))
    ⇈Distr = ( (λ (a , h) 
                  → ( (a , (λ b → fst (h b))) 
                    , λ f → (a , (λ b → snd (h b) (f b))) )) 
             , (λ (a , h) (f , g) b → (f b , g b)) )
    
    ⇈DistrCart : isCartesian ((p ⇈ q) ◃ (p ⇈ r)) ⇈Distr
    ⇈DistrCart (a , h) =
        Iso→isEquiv ( (λ f → ( (λ b → fst (f b)) 
                             , (λ b → snd (f b)) ))
                    , ( (λ (f , g) → refl) 
                      , (λ f → refl) ) )

open ⇈◃ public
```

The fact that `⇈Distr` is Cartesian corresponds to the distributive law of `Π` types over `Σ` types, i.e. $$
\Pi x : A . \Sigma y : B[x] . C[x,y] \simeq \Sigma f : \Pi x : A . B[x] . \Pi x : A . C[x, f(x)]
$$ One may wonder, then, whether this distributive law is somehow related to a distributive law ofg the monad structure on a polynomial universe 𝔲 given by Σ types (as discussed in the previous section) over itself, i.e. a morphism $$ \mathfrak{u} \triangleleft \mathfrak{u} \leftrightarrows \mathfrak{u} \triangleleft \mathfrak{u} $$ subject to certain laws. Indeed, given a Lens `π : (𝔲 ⇈ 𝔲) ⇆ 𝔲` (intuitively – corresponding to the structure of `Π` types in `𝔲`), one can define a morphism of this form as follows:

```agda
distrLaw? : ∀ {ℓ κ} (u : Poly ℓ κ) → (u ⇈ u) ⇆ u
            → (u ◃ u) ⇆ (u ◃ u)
distrLaw? u (π , π♯) = 
    ( (λ (a , b) → π (a , b) , (λ x → a)) 
    , λ (a , b) (f , x) → (x , (π♯ ((a , b)) f x)) )
```

The question then becomes whether this morphism has the structure of a distributive law when `𝔲` has the structure of a polynomial universe with `Σ` types, and `π` is Cartesian (i.e. `𝔲` also has `Π` types). Answering this question in the affirmative shall be our task in the remainder of this section.

As a first step in this direction, we make a perhaps unexpected move of further generalizing the $\upuparrows$ functor to a functor $\mathsf{Tw}(\mathbf{Poly}) \times \mathbf{Poly} \to \mathbf{Poly}$, where $\mathsf{Tw}(\mathbf{Poly})$ is the *twisted arrow category* of $\mathbb{Poly}$, i.e. the category whose objects are lenses and whose morphisms are *twisted* commuting squares of the form $$
\begin{array}{ccc}
p & \leftrightarrows q\\
\donwuparrows & & \downuparrows\\
r & \rightleftarrows & s
\end{array}
$$

As a first step in this direction, we make a perhaps unexpected move of further generalizing the $\upuparrows$ functor to a functor $\mathsf{Tw}(\mathbf{Poly}) \times \mathbf{Poly} \to \mathbf{Poly}$, where $\mathsf{Tw}(\mathbf{Poly})$ is the *twisted arrow category* of $\mathbb{Poly}$, i.e. the category whose objects are lenses and whose morphisms are *twisted* commuting squares of the form $$
\begin{array}{ccc}
p & \leftrightarrows q\\
\donwuparrows & & \downuparrows\\
r & \rightleftarrows & s
\end{array}
$$

```agda
_⇈[_][_]_ : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
            → (p : Poly ℓ κ) (q : Poly ℓ' κ')
            → (p ⇆ q) → (r : Poly ℓ'' κ'')
            → Poly (ℓ ⊔ κ ⊔ ℓ'') (κ' ⊔ κ'')
(A , B) ⇈[ (C , D) ][ (f , f♯) ] (E , F) =
   ( (Σ A (λ a → B a → E)) 
   , (λ (a , ε) → (d : D (f a)) → F (ε (f♯ a d))))

module ⇈[]Functor {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 κ0 κ1 κ2 κ3 κ4 κ5}
          {p : Poly ℓ0 κ0} {p' : Poly ℓ3 κ3}
          (q : Poly ℓ1 κ1) {q' : Poly ℓ4 κ4}
          {r : Poly ℓ2 κ2} (r' : Poly ℓ5 κ5)
          (f : p ⇆ q) (f' : p' ⇆ q')
          (g : p ⇆ p') (h : q' ⇆ q) (k : r ⇆ r')
          (e : EqLens q f (comp q g (comp q f' h))) where

    ⇈[]Lens : (p ⇈[ q ][ f ] r) ⇆ (p' ⇈[ q' ][ f' ] r')
    ⇈[]Lens = 
        ( (λ (a , γ) → (fst g a , λ x → fst k (γ (snd g a x)))) 
        , λ (a , γ) Ϝ x →
            snd k (γ (snd f a x)) 
               (transp (λ y → snd r' (fst k (γ y))) 
                       (sym (snd e a x)) 
                       (Ϝ (snd h (fst f' (fst g a)) 
                              (transp (snd q) (fst e a) x)))) )
```

Straightforwardly, we have that `p ⇈ q = p ⇈[ p ][ id p ] q`. In particular, we have `⇈Lens p p' q q' f f' e g = ⇈[]Lens p p' p p' q q' (id p) (id p') f f' g e`, which serves to motivate the definition of `⇈Lens` in terms of morphisms equipped with left inverses.

The functor `_⇈[_][_]_` defined above moreover preserves Cartesian morphisms in all of its arguments, and so restricts to a functor $\mathsf{Tw}(\mathbf{Poly}^{\mathbf{Cart}}) \times \mathbf{Poly}^\mathbf{Cart} \to \mathbf{Poly}^\mathbf{Cart}$.

```agda
    ⇈[]LensCart : isCartesian q h → isCartesian r' k
                  → isCartesian (p' ⇈[ q' ][ f' ] r') ⇈[]Lens
    ⇈[]LensCart ch ck (a , γ) = 
        compIsEquiv 
            (PostCompEquiv (λ x → snd k (γ (snd f a x))) 
                           (λ x → ck (γ (snd f a x)))) 
            (compIsEquiv 
                (PostCompEquiv 
                    (λ x → transp (λ y → snd r' (fst k (γ y))) 
                                  (sym (snd e a x))) 
                    (λ x → transpIsEquiv (sym (snd e a x)))) 
                (compIsEquiv 
                    (PreCompEquiv (transp (snd q) (fst e a)) 
                                  (transpIsEquiv (fst e a))) 
                    (PreCompEquiv (λ x → snd h (fst f' (fst g a)) x) 
                                  (ch (fst f' (fst g a))))))

open ⇈[]Functor public
```

Moreover, all the properties of `_⇈_` noted above generalize to `_⇈[_][_]_`. For instance, we now have natural transformations $$
\mathbb{y} {\upuparrows}[\text{id}_{\mathbb{y}}] p \to p
$$ $$
(p \triangleleft r) {\upuparrows}[f \triangleleft g] q \to p {\upuparrows}[f] (r {\upuparrows}[g] q)
$$ as follows:

```agda
𝕪⇈[] : ∀ {ℓ κ} (p : Poly ℓ κ) → (𝕪 ⇈[ 𝕪 ][ (id 𝕪) ] p) ⇆ p
𝕪⇈[] p = ((λ (_ , γ) → γ tt) , λ (_ , γ) Ϝ _ → Ϝ)

⇈[]Curry : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 κ0 κ1 κ2 κ3 κ4}
           → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) 
           → (r : Poly ℓ2 κ2) (s : Poly ℓ3 κ3)
           → (t : Poly ℓ4 κ4)
           → (f : p ⇆ q) (g : r ⇆ s)
           → ((p ◃ r) ⇈[ q ◃ s ][ f ◃◃[ s ] g ] t) 
             ⇆ (p ⇈[ q ][ f ] (r ⇈[ s ][ g ] t))
⇈[]Curry p q r s t f g = 
    ( (λ ((a , h) , k) → a , (λ b → (h b) , (λ d → k (b , d)))) 
    , λ ((a , h) , k) Ϝ (b , d) → Ϝ b d)
```

And similarly, we have natural transformations $$
p {\upuparrows}[f] \mathbb{y} → \mathbb{y}
$$ $$
p {\upuparrows}[g \circ f] (r \triangleleft s) \to (p {\upuparrows}[f] r) \triangleleft (q {\upuparrows}[g] s)
$$

```agda
⇈[]𝕪 : ∀ {ℓ0 κ0 ℓ1 κ1} (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) 
       → (f : p ⇆ q) → (p ⇈[ q ][ f ] 𝕪) ⇆ 𝕪
⇈[]𝕪 p q f = ((λ _ → tt) , λ _ _ _ → tt)
      

⇈[]Distr : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 κ0 κ1 κ2 κ3 κ4}
           → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
           → (s : Poly ℓ3 κ3) (t : Poly ℓ4 κ4)
           → (f : p ⇆ q) (g : q ⇆ r)
           → (p ⇈[ r ][ comp r f g ] (s ◃ t)) 
             ⇆ ((p ⇈[ q ][ f ] s) ◃ (q ⇈[ r ][ g ] t))
⇈[]Distr p q r s t (f , f♯) (g , g♯) = 
    ( (λ (a , h) → (a , (λ x → fst (h x))) , λ k1 → f a , λ x → snd (h (f♯ a x)) (k1 x)) 
    , λ (a , h) (k1 , k2) d → (k1 (g♯ (f a) d)) , k2 d )
```

As we shall now see, these structures on `_⇈[_][_]_` are intimately connected to a class of morphisms in $\mathbf{Poly}$, which we call *distributors*.

## Distributors

Given polynomials `p,q,r,s`, a *distributor* of `p,q` over `r,s` is a morphism of the form `(p ◃ r) ⇆ (s ◃ q)` in $\mathbf{Poly}$. The name "distributor" is here drawn from the fact that, given polynomial monads `m,n` with `ηₘ : 𝕪 ⇆ m, ηₙ : 𝕪 ⇆ n` and `μₘ : (m ◃ m) ⇆ m, μₙ : (n ◃ n) ⇆ n`, a *distributive law* of `m` over `n` consists of a distributor of `n,n` over `n,n` (i.e. a morphism `(n ◃ m) ⇆ (m ◃ n)`) such that the following diagrams commute:

...

By inspection, it can be seen that all the composite morphisms required to commute by the above diagrams are themselves distributors of various forms. Understanding the closure properties of such distributors that give rise to these diagrams, then, will be a central aim of this section.

Moreover, for any polynomial `u` with `π : (u ⇈ u) ⇆ u`, the morphism `distrLaw? u π` defined above is a distributor of `u,u` over itself. In fact, we can straightforwardly generalize the construction of `distrLaw?` to a transformation $$
(p ~{\upuparrows}[q][f] r) \leftrightarrows s \implies (p \triangleleft r) \leftrightarrows (s \triangleleft q)
$$ as follows:

```agda
⇈→Distributor : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 κ0 κ1 κ2 κ3}
                → {p : Poly ℓ0 κ0} (q : Poly ℓ1 κ1)
                → (r : Poly ℓ2 κ2) {s : Poly ℓ3 κ3}
                → {f : p ⇆ q}
                → (p ⇈[ q ][ f ] r) ⇆ s
                → (p ◃ r) ⇆ (s ◃ q)
⇈→Distributor q r {f = (f , f♯)} (g , g♯) =
    ( (λ (a , h) → g (a , h) , λ d' → f a) 
    , λ (a , h) (d' , d)
        → f♯ a d , g♯ (a , h) d' d)
```

Hence to show that the above-given diagrams commute for the candidate distributive law `distrLaw? u π` given above, it suffices to show that the distributors required to commute by these diagrams themselves arise – under the above-defined transformation – from Cartesian morphisms of the form `p ⇈[ q ][ f ] r ⇆ u`, which, if `u` is a polynomial universe, are necessarily equal.

First of all, any distributor $(p \triangleleft r) \leftrightarrows (s \triangleleft q)$ may be extended along morphisms `p' ⇆ p, q ⇆ q', r' ⇆ r, s ⇆ s'` to a distributor $(p' \triangleleft r') \leftrightarrows (s' \triangleleft q')$ by forming the composite $$
p' \triangleleft r' \xrightarrow{} p \triangleleft r \xrightarrow{} s \triangleleft q \xrightarrow{} s' \triangleleft q'
$$

```agda
module DistributorLens {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 ℓ7
                        κ0 κ1 κ2 κ3 κ4 κ5 κ6 κ7}
                       {p : Poly ℓ0 κ0} {p' : Poly ℓ4 κ4}
                       {q : Poly ℓ1 κ1} {q' : Poly ℓ5 κ5}
                       {r : Poly ℓ2 κ2} {r' : Poly ℓ6 κ6}
                       {s : Poly ℓ3 κ3} {s' : Poly ℓ7 κ7}
                       (g : p' ⇆ p) (h : q ⇆ q') 
                       (k : r' ⇆ r) (l : s ⇆ s') where

    distrLens : (p ◃ r) ⇆ (s ◃ q) → (p' ◃ r') ⇆ (s' ◃ q')
    distrLens j = 
        comp (s' ◃ q') (g ◃◃[ r ] k) 
             (comp ((s' ◃ q')) j 
                   (l ◃◃[ q' ] h))
```

The corresponding construction on morphisms out of `_⇈[_][_]_` is given by forming the composite $$
p' ~ {\upuparrows}[q'][h \circ f \circ g] ~ r' \leftrightarrows p {\upuparrows}[q][f] ~ r \leftrightarrows s \leftrightarrows s'
$$

```agda
    ⇈→DistributorLens : {f : p ⇆ q} → (p ⇈[ q ][ f ] r) ⇆ s 
                        → (p' ⇈[ q' ][ comp q' g (comp q' f h) ] r') ⇆ s'
    ⇈→DistributorLens {f = f} j = 
        comp s' (⇈[]Lens q' r (comp q' g (comp q' f h)) f 
                         g h k ((λ a → refl) , (λ a d → refl))) 
             (comp s' j l)

    ⇈→DistributorLens≡ : {f : p ⇆ q} (j : (p ⇈[ q ][ f ] r) ⇆ s)
                         → distrLens (⇈→Distributor q r j) 
                           ≡ ⇈→Distributor q' r' (⇈→DistributorLens j)
    ⇈→DistributorLens≡ j = refl

open DistributorLens public
```

Similarly, there are two distinct ways of composing jump morphisms: 

1. Given jump morphisms $j1 : s \xleftarrow{p \xleftarrow{f} q} t$ and $j2 : u \xleftarrow{q \xrightarrow{g} r} v$, we obtain a Jump structure $s \triangleleft u \xleftarrow{p \xrightarrow{g \circ f} r} t \triangleleft v$ on the composite $$
p ◃ (s \triangleleft u) \simeq (p \triangleleft s) \triangleleft u \xrightarrow{j1 \triangleleft u} (t \triangleleft q) \triangleleft u \simeq t \traingleleft (q \triangleleft u) \xrightarrow{j2} t \triangleleft (v \triangleleft r) \simeq (t \triangleleft v) \triangleleft r
$$

```agda
module DistributorComp1 {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 κ0 κ1 κ2 κ3 κ4 κ5 κ6}
                        {p : Poly ℓ0 κ0} {q : Poly ℓ1 κ1} {r : Poly ℓ2 κ2}
                        {s : Poly ℓ3 κ3} {t : Poly ℓ4 κ4}
                        {u : Poly ℓ5 κ5} {v : Poly ℓ6 κ6} where

    distrComp1 : (p ◃ s) ⇆ (t ◃ q) → (q ◃ u) ⇆ (v ◃ r)
                 → (p ◃ (s ◃ u)) ⇆ ((t ◃ v) ◃ r)
    distrComp1 h k = 
        comp ((t ◃ v) ◃ r) (◃assoc⁻¹ p s u) 
             (comp ((t ◃ v) ◃ r) (h ◃◃[ u ] (id u)) 
                   (comp ((t ◃ v) ◃ r) (◃assoc t q u) 
                         (comp ((t ◃ v) ◃ r) ((id t) ◃◃[ (v ◃ r) ] k) 
                               (◃assoc⁻¹ t v r))))
```

The corresponding construction on morphisms `(p ⇈[ q ][ f ] s) ⇆ t` and `(q ⇈[ r ][ g ] u) ⇆ v` is to form the following composite with the colaxator of `_⇈[_][_]_`: $$
p {\upuparrows}[r][g \circ f] (s \triangleleft u) \leftrightarrows (p {\upuparrows}[q][f] s) \triangleleft (q {\upuparrows}[r][g] u) \leftrightarrows t \triangleleft v
$$

```agda
    ⇈→DistributorComp1 : {f : p ⇆ q} {g : q ⇆ r} 
                         → (p ⇈[ q ][ f ] s) ⇆ t 
                         → (q ⇈[ r ][ g ] u) ⇆ v
                         → (p ⇈[ r ][ comp r f g ] (s ◃ u)) ⇆ (t ◃ v)
    ⇈→DistributorComp1 {f = f} {g = g} h k = 
        comp (t ◃ v) (⇈[]Distr p q r s u f g) 
             (h ◃◃[ v ] k)

    ⇈→DistributorComp1≡ : {f : p ⇆ q} {g : q ⇆ r} 
                          (h : (p ⇈[ q ][ f ] s) ⇆ t)
                          (k : (q ⇈[ r ][ g ] u) ⇆ v)
                          → distrComp1 (⇈→Distributor q s h) (⇈→Distributor r u k)
                            ≡ ⇈→Distributor r (s ◃ u) (⇈→DistributorComp1 h k)
    ⇈→DistributorComp1≡ h k = refl
    
open DistributorComp1 public
```

2. Given jump morphisms $j1 : t \xleftarrow{p \xrightarrow{f} q} u$ and $j2 : s \xleftarrow{r \xrightarrow{g} s} t$, we obtain a jump structure $s \xleftarrow{p \triangleleft r \xrightarrow{f \triangleleft g} q \triangleleft s} u$ on the composite $$
(p \triangleleft r) \triangleleft s \simeq p \triangleleft (r \triangleleft s) \xrightarrow{p \triangleleft j2} p \triangleleft (t \triangleleft s) \simeq (p \triangleleft t) \triangleleft s \xrightarrow{j1} (u \triangleleft q) \triangleleft s \simeq u \triangleleft (q \triangleleft s)
$$

```agda

```