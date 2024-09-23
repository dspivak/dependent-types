```agda
{-# OPTIONS --without-K --rewriting #-}
module part4 where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import part1
open import part2
open import part3
```

# $\Pi$-Types, Jump Monads & Distributive Laws

We have so far considered how polynomial universes may be equipped with structure to interpret the unit type and dependent pair types. We have not yet, however, said much in the way of *dependent function types.* In order to rectify this omission, it will first be prudent to consider some additional structure on the category of polynomial functors – specifically a new functor ${\upuparrows}[\_] : \mathsf{Tw}(\mathbf{Poly}) \times \mathbf{Poly} \to \mathbf{Poly}$ that plays a similar role for `Π` types as the composition $\triangleleft : \mathbf{Poly} \times \mathbf{Poly} \to \mathbf{Poly}$ played for `Σ` types, and which in turn bears a close connection to a class of structured morphisms in $\mathbf{Poly}$, which we refer to as *jump morphisms.*

## The $\upuparrows$ and ${\upuparrows}[\_]$ Functors

The $\upuparrows$ functor can be loosely defined as the solution to the following problem: given a polynomial universe `𝔲`, find `𝔲 ⇈ 𝔲` such that `𝔲` classifies `𝔲 ⇈ 𝔲` if and only if `𝔲` has the structure to interpret `Π` types (in the same way that `𝔲` classifies `𝔲 ◃ 𝔲` if and only if `𝔲` has the structure to interpret `Σ` types). Generalizing this to arbitrary pairs of polynomials $p = (A , B), ~ q = (C , D)$ then yields the following formula for $p \upuparrows q$: $$
p \upuparrows q = \sum_{(a , f) : \sum_{a : A} C^{B(a)}} y^{\prod_{b : B(a)} D(f(b))}
$$

```agda
_⇈_ : ∀ {ℓ ℓ' κ κ'} → Poly ℓ κ → Poly ℓ' κ' → Poly (ℓ ⊔ κ ⊔ ℓ') (κ ⊔ κ')
(A , B) ⇈ (C , D) = 
    ( Σ A (λ a → B a → C) 
    , (λ (a , f) → (b : B a) → D (f b)))
```

Note that this construction is straightforwardly functorial with respect to arbitrary lenses in its 2nd argument. Functoriality of the 1st argument is trickier, however. For reasons that will become apparent momentarily, we define the functorial action $p \upuparrows q \leftrightarrows p' \upuparrows q$ of $\upuparrows$ on a lens $f : p \leftrightarrows p'$ equipped with a left inverse $f' : p' \leftrightarrows p$, i.e. such that $f' \circ f = \text{id}_p$.

```agda
⇈Lens : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
        → (p : Poly ℓ κ) (q : Poly ℓ' κ') 
        → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
        → (f : p ⇆ r) (f' : r ⇆ p) 
        → EqLens p p (id p) (comp p r p f f')
        → (g : q ⇆ s) → (p ⇈ q) ⇆ (r ⇈ s)
⇈Lens p q r s (f , f♯) (f' , f'♯) e (g , g♯) = 
    ( (λ (a , γ) → (f a , (λ x → g (γ (f♯ a x)))))
    , λ (a , γ) Ϝ x → g♯ (γ x) (transp (λ y → snd s (g (γ y))) (sym (snd (e a) x)) (Ϝ (f'♯ (f a) (transp (snd p) (fst (e a)) x)))))
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

Although it is clear enough that the $\upuparrows$ functor serves its intended purpose of characterizing `Π` types in polynomial universes, its construction seems somewhat more ad hoc than that of $\triangleleft$, which similarly characterized `Σ` types in polynomial universes while arising quite naturally from composition of polynomial functors. We would like to better understand what additional properties $\upuparrows$ must satisfy, and how these in turn are reflected as properties of polynomial universes with `Π` types. In fact, we will ultimately show that this construction is intimately linked with a quite simple structure on polynomial universes `𝔲`, namely a *distributive law* of `𝔲` (viewed as a monad) over itself, satisfying some additional requirements. Before that, however, we note some other key properties of $\upuparrows$.

Specifically, let $\mathbf{Poly}_{R}$ be the wide subcategory of $\mathbf{Poly}$ spanned by morphisms equipped with left inverses (hence which are themselves right inverses). Straightforwardly, $\triangleleft$ restricts to a monoidal product on $\mathbf{Poly}_R$, since it is functorial in both arguments and must preserve left/right inverses. Hence $\upuparrows$ can be viewed as a functor $\mathbf{Poly}_R \times \mathbf{Poly} \to \mathbf{Poly}$. Then $\upuparrows$ moreover naturally carries the structure of an *action* on $\mathbf{Poly}$ of the monoidal category $\mathbf{Poly}_R$ equipped with $\triangleleft$, in that there are natural isomorphisms $$
\mathbb{y} \upuparrows p \simeq p $$ $$
(p \triangleleft q) \upuparrows r \simeq p \upuparrows (q \upuparrows r)
$$

```agda
𝕪⇈ : ∀ {ℓ κ} (p : Poly ℓ κ) → (𝕪 ⇈ p) ⇆ p
𝕪⇈ p = ( (λ (tt , a) → a tt) 
       , λ (tt , a) b tt → b)

𝕪⇈Vert : ∀ {ℓ κ} (p : Poly ℓ κ) → isVertical (𝕪 ⇈ p) p (𝕪⇈ p)
𝕪⇈Vert p = Iso→isEquiv ( (λ x → tt , (λ tt → x)) 
                       , ( (λ a → refl) 
                       , λ b → refl))

𝕪⇈Cart : ∀ {ℓ κ} (p : Poly ℓ κ) → isCartesian (𝕪 ⇈ p) p (𝕪⇈ p)
𝕪⇈Cart p (tt , x) = 
    Iso→isEquiv ( (λ Ϝ → Ϝ tt) 
                , ( (λ a → refl) 
                  , λ b → refl))

⇈Curry : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
         → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
         → ((p ◃ q) ⇈ r) ⇆ (p ⇈ (q ⇈ r))
⇈Curry p q r = ( (λ ((a , h) , k) → a , (λ b → (h b) , (λ d → k (b , d)))) 
               , λ ((a , h) , k) f (b , d) → f b d)

⇈CurryVert : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
             → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
             → isVertical ((p ◃ q) ⇈ r) (p ⇈ (q ⇈ r)) (⇈Curry p q r)
⇈CurryVert p q r = 
    Iso→isEquiv ((λ (a , h) → (a , (λ x → fst (h x))) , (λ (x , y) → snd (h x) y)) 
                , ( (λ a → refl) 
                  , λ b → refl))

⇈CurryCart : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
             → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
             → isCartesian ((p ◃ q) ⇈ r) (p ⇈ (q ⇈ r)) (⇈Curry p q r)
⇈CurryCart p q r ((a , h) , k) = 
    Iso→isEquiv ( (λ f b d → f (b , d)) 
                , ( (λ f → refl) 
                  , λ f → refl))
```

Moreover, $\upuparrows$ is colax with respect to $\triangleleft$ in its second argument, in that there are natural transformations $$
p \upuparrows \mathbb{y} → \mathbb{y}
$$ $$
p \upuparrows (q \triangleleft r) \to (p \upuparrows q) \triangleleft (p \upuparrows r)
$$

```agda
⇈𝕪 : ∀ {ℓ κ} (p : Poly ℓ κ) → (p ⇈ 𝕪) ⇆ 𝕪
⇈𝕪 p = ( (λ (a , γ) → tt) 
       , λ (a , γ) tt b → tt )

⇈Distr : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
         → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
         → (p ⇈ (q ◃ r)) ⇆ ((p ⇈ q) ◃ (p ⇈ r))
⇈Distr p q r = ( (λ (a , h) → (a , (λ b → fst (h b))) , λ f → a , (λ b → snd (h b) (f b))) 
               , λ (a , h) (f , g) b → (f b) , (g b) )
```

Moreover, both of these natural transformations are Cartesian.

```agda
⇈𝕪Cart : ∀ {ℓ κ} (p : Poly ℓ κ) → isCartesian (p ⇈ 𝕪) 𝕪 (⇈𝕪 p)
⇈𝕪Cart p (x , γ) = 
    Iso→isEquiv ( (λ x → tt) 
                , ( (λ a → refl) 
                  , λ b → refl))

⇈DistrCart : ∀ {ℓ0 ℓ1 ℓ2 κ0 κ1 κ2}
             → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
             → isCartesian (p ⇈ (q ◃ r)) ((p ⇈ q) ◃ (p ⇈ r)) (⇈Distr p q r)
⇈DistrCart p q r (a , h) =
    Iso→isEquiv ( (λ f → (λ b → fst (f b)) , (λ b → snd (f b))) 
                , ( (λ (f , g) → refl) 
                  , λ f → refl))
```

The fact that `⇈Distr` is Cartesian corresponds to the distributive law of `Π` types over `Σ` types, i.e. $$
\Pi x : A . \Sigma y : B[x] . C[x,y] \simeq \Sigma f : \Pi x : A . B[x] . \Pi x : A . C[x, f(x)]
$$ One may wonder, then, whether this distributive law is somehow related to a distributive law ofg the monad structure on a polynomial universe 𝔲 given by Σ types (as discussed in the previous section) over itself, i.e. a morphism $$ \mathfrak{u} \triangleleft \mathfrak{u} \leftrightarrows \mathfrak{u} \triangleleft \mathfrak{u} $$ subject to certain laws. Indeed, given a Lens `π : (𝔲 ⇈ 𝔲) ⇆ 𝔲` (intuitively – corresponding to the structure of `Π` types in `𝔲`), one can define a morphism of this form as follows:

```agda
distrLaw? : ∀ {ℓ κ} (𝔲 : Poly ℓ κ)
            → (𝔲 ⇈ 𝔲) ⇆ 𝔲
            → (𝔲 ◃ 𝔲) ⇆ (𝔲 ◃ 𝔲)
distrLaw? 𝔲 (π , π♯) = 
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

```agda
_⇈[_][_]_ : ∀ {ℓ ℓ' ℓ'' κ κ' κ''}
            → (p : Poly ℓ κ) (q : Poly ℓ' κ')
            → (p ⇆ q) → (r : Poly ℓ'' κ'')
            → Poly (ℓ ⊔ κ ⊔ ℓ'') (κ' ⊔ κ'')
(A , B) ⇈[ (C , D) ][ (f , f♯) ] (E , F) =
   ( (Σ A (λ a → B a → E)) 
   , (λ (a , ε) → (d : D (f a)) → F (ε (f♯ a d))))

⇈[]Lens : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 κ0 κ1 κ2 κ3 κ4 κ5}
          → (p : Poly ℓ0 κ0) (p' : Poly ℓ3 κ3)
          → (q : Poly ℓ1 κ1) (q' : Poly ℓ4 κ4)
          → (r : Poly ℓ2 κ2) (r' : Poly ℓ5 κ5)
          → (f : p ⇆ q) (f' : p' ⇆ q')
          → (g : p ⇆ p') (h : q' ⇆ q) (k : r ⇆ r')
          → EqLens p q f (comp p p' q g (comp p' q' q f' h))
          → (p ⇈[ q ][ f ] r) ⇆ (p' ⇈[ q' ][ f' ] r')
⇈[]Lens p p' q q' r r' (f , f♯) (f' , f'♯) (g , g♯) (h , h♯) (k , k♯) e = 
    ( (λ (a , γ) → (g a , λ x → k (γ (g♯ a x)))) 
    , λ (a , γ) Ϝ x →
        k♯ (γ (f♯ a x)) 
           (transp (λ y → snd r' (k (γ y))) 
                   (sym (snd (e a) x)) 
                   (Ϝ (h♯ (f' (g a)) 
                          (transp (snd q) (fst (e a)) x)))) )

postulate
    funext : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
             → ((x : A) → f x ≡ g x) → f ≡ g
    funextr : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
              → (e : (x : A) → f x ≡ g x) → coAp (funext e) ≡ e
    funextl : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {f g : (x : A) → B x}
              → (e : f ≡ g) → funext (coAp e) ≡ e

transpD : ∀ {ℓ κ} {A : Type ℓ} {B : A → Type κ} {a a' : A}
          → (f : (x : A) → B x) (e : a ≡ a')
          → transp B e (f a) ≡ f a'
transpD f refl = refl

transpHAdj : ∀ {ℓ ℓ' κ} {A : Type ℓ} {B : Type ℓ'} 
            → {C : B → Type κ} {a : A}
            → {g : A → B} {h : B → A} 
            → (f : (x : A) → C (g x)) 
            → (e : (y : B) → g (h y) ≡ y)
            → (e' : (x : A) → h (g x) ≡ x)
            → (e'' : (x : A) → e (g x) ≡ ap g (e' x))
            → transp C (e (g a)) (f (h (g a))) ≡ f a
transpHAdj {C = C} {a = a} {g = g} {h = h} f e e' e'' = 
    transp C (e (g a)) (f (h (g a)))               
        ≡〈 ap (λ ee → transp C ee (f (h (g a)))) (e'' a) 〉 
    (transp C (ap g (e' a)) (f (h (g a))) 
        ≡〈 sym (transpAp C g (e' a) (f (h (g a)))) 〉 
    ((transp (λ x → C (g x)) (e' a) (f (h (g a)))) 
        ≡〈 transpD f (e' a) 〉
    ((f a) □)))

PreCompEquiv : ∀ {ℓ ℓ' κ} {A : Type ℓ} {B : Type ℓ'} {C : B → Type κ}
               → (f : A → B) → isEquiv f 
               → isEquiv {A = (b : B) → C b} 
                         {B = (a : A) → C (f a)} 
                         (λ g → λ a → g (f a))
PreCompEquiv {C = C} f ef =
    let (f⁻¹ , l , r , e) = Iso→HAdj (isEquiv→Iso ef) 
    in Iso→isEquiv ( (λ g b → transp C (r b) (g (f⁻¹ b))) 
                   , ( (λ g → funext (λ b → transpD g (r b))) 
                     , λ g → funext (λ a → transpHAdj g r l (λ x → sym (e x)))))

PostCompEquiv : ∀ {ℓ κ κ'} {A : Type ℓ} {B : A → Type κ} {C : A → Type κ'}
                → (f : (x : A) → B x → C x) → ((x : A) → isEquiv (f x))
                → isEquiv {A = (x : A) → B x} 
                          {B = (x : A) → C x}
                          (λ g x → f x (g x))
PostCompEquiv f ef = 
    ( ( (λ g x → fst (fst (ef x)) (g x))
      , λ g → funext (λ x → snd (fst (ef x)) (g x))))
    , ( (λ g x → fst (snd (ef x)) (g x)) 
      , λ g → funext (λ x → snd (snd (ef x)) (g x)))

⇈[]LensCart : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 κ0 κ1 κ2 κ3 κ4 κ5}
          → (p : Poly ℓ0 κ0) (p' : Poly ℓ3 κ3)
          → (q : Poly ℓ1 κ1) (q' : Poly ℓ4 κ4)
          → (r : Poly ℓ2 κ2) (r' : Poly ℓ5 κ5)
          → (f : p ⇆ q) (f' : p' ⇆ q')
          → (g : p ⇆ p') (h : q' ⇆ q) (k : r ⇆ r')
          → isCartesian q' q h → isCartesian r r' k
          → (e : EqLens p q f (comp p p' q g (comp p' q' q f' h)))
          → isCartesian (p ⇈[ q ][ f ] r) (p' ⇈[ q' ][ f' ] r')
                        (⇈[]Lens p p' q q' r r' f f' g h k e)
⇈[]LensCart p p' q q' r r' (f , f♯) (f' , f'♯) (g , g♯) (h , h♯) (k , k♯) ch ck e (a , γ) = 
    compIsEquiv (λ Ϝ x → k♯ (γ (f♯ a x)) (Ϝ x)) (λ Ϝ x → transp (λ y → snd r' (k (γ y))) (sym (snd (e a) x)) (Ϝ (h♯ (f' (g a)) (transp (snd q) (fst (e a)) x)))) (PostCompEquiv (λ x → k♯ (γ (f♯ a x))) (λ x → ck (γ (f♯ a x)))) (compIsEquiv (λ Ϝ x → transp (λ y → snd r' (k (γ y))) (sym (snd (e a) x)) (Ϝ x)) (λ Ϝ x → Ϝ (h♯ (f' (g a)) (transp (snd q) (fst (e a)) x))) (PostCompEquiv (λ x → transp (λ y → snd r' (k (γ y))) (sym (snd (e a) x))) (λ x → transpIsEquiv (sym (snd (e a) x)))) (compIsEquiv (λ Ϝ x → Ϝ (transp (snd q) (fst (e a)) x)) (λ Ϝ x → Ϝ (h♯ (f' (g a)) x)) (PreCompEquiv (transp (snd q) (fst (e a))) (transpIsEquiv (fst (e a)))) (PreCompEquiv (λ x → h♯ (f' (g a)) x) (ch (f' (g a))))))

{- ⇈[]Lens≡ : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 κ0 κ1 κ2 κ3}
           → (p : Poly ℓ0 κ0) (p' : Poly ℓ2 κ2)
           → (q : Poly ℓ1 κ1) (q' : Poly ℓ3 κ3)
           → (f : p ⇆ p') (g : q ⇆ q')
           → (cf : isCartesian p p' f)
           → EqLens (p ⇈ q) (p' ⇈ q')
                    (⇈Lens p q p' q' f cf g)
                    (⇈[]Lens p p' p p' q q' (id p) (id p') f (Cart→Chart p p' f cf) g (λ a → refl , (λ d → sym (snd (snd (cf a)) d))))
⇈[]Lens≡ p p' q q' f g cf = λ a → refl , (λ b → refl) -}
```

Straightforwardly, we have that `p ⇈ q = p ⇈[ p ][ id p ] q`. In particular, we have `⇈Lens p p' q q' f f' e g = ⇈[]Lens p p' p p' q q' (id p) (id p') f f' g e`, which serves to motivate the definition of `⇈Lens` in terms of morphism equipped with left inverses.

Moreover, all the properties of `_⇈_` noted above generalize to `_⇈[_][_]_`. For instance, we now have natural isomorphisms $$
\mathbb{y} {\upuparrows}[\text{id}_{\mathbb{y}}] p \simeq p
$$ $$
(p \triangleleft r) {\upuparrows}[f \triangleleft g] q \simeq p {\upuparrows}[f] (r {\upuparrows}[g] q)
$$

```agda
⇈[]Curry : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 κ0 κ1 κ2 κ3 κ4}
           → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) 
           → (r : Poly ℓ2 κ2) (s : Poly ℓ3 κ3)
           → (t : Poly ℓ4 κ4)
           → (f : p ⇆ q) (g : r ⇆ s)
           → ((p ◃ r) ⇈[ q ◃ s ][ ◃Lens p q r s f g ] t) 
             ⇆ (p ⇈[ q ][ f ] (r ⇈[ s ][ g ] t))
⇈[]Curry p q r s t f g = 
    ( (λ ((a , h) , k) → a , (λ b → (h b) , (λ d → k (b , d)))) 
    , λ ((a , h) , k) Ϝ (b , d) → Ϝ b d)
```

And similarly, we have Cartesian natural transformations $$
p {\upuparrows}[f] \mathbb{y} → \mathbb{y}
$$ $$
p {\upuparrows}[g \circ f] (r \triangleleft s) \to (p {\upuparrows}[f] r) \triangleleft (q {\upuparrows}[g] s)
$$

```agda
⇈[]Distr : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 κ0 κ1 κ2 κ3 κ4}
           → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
           → (s : Poly ℓ3 κ3) (t : Poly ℓ4 κ4)
           → (f : p ⇆ q) (g : q ⇆ r)
           → (p ⇈[ r ][ comp p q r f g ] (s ◃ t)) 
             ⇆ ((p ⇈[ q ][ f ] s) ◃ (q ⇈[ r ][ g ] t))
⇈[]Distr p q r s t (f , f♯) (g , g♯) = 
    ( (λ (a , h) → (a , (λ x → fst (h x))) , λ k1 → f a , λ x → snd (h (f♯ a x)) (k1 x)) 
    , λ (a , h) (k1 , k2) d → (k1 (g♯ (f a) d)) , k2 d )
```

To see why this construction is important, we now introduce the novel concept of a *jump morphism* in $\mathbf{Poly}$.

## Jump Morphisms

Given a lens $(f , f^\sharp) : p \leftrightarrows q$ with $p = (A , B)$ and $q = (C , D)$, a *jump morphism* $(g, g^\sharp) : r \xrightarrow{p \xrightarrow{(f , f^\sharp)} q} s$ for $r = (A' , B')$ and $s = (C' , D')$ is a lens $(g, g^\sharp) : p \triangleleft r \leftrightarrows s \triangleleft q$ equipped with identities `\pi_2(g(a , h)(d')) = f(a)` for all $a : A$ with $h : {A'}^{B(a)}$ and $d' : D'(\pi_1(g(a,h)))$, and $\pi_1(g^\sharp(a,h)(d',d)) = f^\sharp(a , d)$ for all $a : A$ with $h : {A'}^{B(a)}$ and $d : D(f(a))$ and $d' : D'(g(a , h))$.

```agda
Jump : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
       → (p : Poly ℓ κ) (q : Poly ℓ' κ')
       → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
       → (p ⇆ q)
       → (p ◃ r) ⇆ (s ◃ q)
       → Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ κ ⊔ κ' ⊔ κ''')
Jump (A , B) (C , D) (A' , B') (C' , D') (f , f♯) (g , g♯) =
    Σ ((a : A) (h : B a → A') 
       (d' : D' (fst (g (a , h)))) 
        → snd (g (a , h)) d' ≡ f a) 
       λ e → (a : A) (h : B a → A') 
             (d' : D' (fst (g (a , h))))
             (d : D (snd (g (a , h)) d'))
             → fst (g♯ (a , h) (d' , d)) 
               ≡ f♯ a (transp D (e a h d') d)
```

We can think of a jump morphism $g : r \xrightarrow{p \xrightarrow{f} q} s$ as one which applies $f$ to the components of $p$ and $q$ while *jumping over* its action on the components of $r$ and $s$. By construction the morphism `distrLaw?` defined above can naturally be equipped with the structure of a jump morphism with respect to the identity morphism on a polynomial unvierse $𝔲$:

```agda
distrLaw?Jump : ∀ {ℓ κ} (𝔲 : Poly ℓ κ)
                → (π : (𝔲 ⇈ 𝔲) ⇆ 𝔲)
                → Jump 𝔲 𝔲 𝔲 𝔲 (id 𝔲) (distrLaw? 𝔲 π)
distrLaw?Jump 𝔲 π = (λ a h d' → refl) , (λ a h d' d → refl)
```

Another example of a jump morphism is given, for any polynomial $p$, by the composite $$
\mathbb{y} \triangleleft p \leftrightarrows p \leftrightarrows p \triangleleft \mathbb{y}
$$ of the left unitor for $◃$ with the inverse of the right unitor. This also naturally carries the structure of a Jump morphism with respect to the identity on $\mathbb{y}$ as follows:

```agda
𝕪Jump : ∀ {ℓ κ} (p : Poly ℓ κ)
        → Jump 𝕪 𝕪 p p (id 𝕪) 
               (comp (𝕪 ◃ p) p (p ◃ 𝕪)
                     (◃unitl p) (◃unitr⁻¹ p))
𝕪Jump p = (λ a h d' → refl) , (λ a h d' d → refl)
```

By application of function extensionality, we have the following type of equality proofs for jump morphisms:

```agda
EqJump1 : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
          → (p : Poly ℓ κ) (q : Poly ℓ' κ')
          → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
          → (g g' : (p ◃ r) ⇆ (s ◃ q))
          → Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ ℓ''' ⊔ κ ⊔ κ' ⊔ κ'' ⊔ κ''')
EqJump1 (A , B) (C , D) (A' , B') (C' , D') (g , g♯) (g' , g'♯) =
    (a : A) (h : B a → A')
    → Σ (fst (g (a , h)) ≡ fst (g' (a , h)))
        (λ e1 → (d' : D' (fst (g (a , h))))
              → Σ ((snd (g (a , h)) d' ≡ snd (g' (a , h)) (transp D' e1 d')))
                  (λ e2 → (d : D (snd (g (a , h)) d'))
                        → Σ (fst (g♯ (a , h) (d' , d)) ≡ fst (g'♯ (a , h) (transp D' e1 d' , transp D e2 d)))
                            λ e3 → transp (λ x → B' (h x)) e3 (snd (g♯ (a , h) (d' , d))) 
                                   ≡ snd (g'♯ (a , h) (transp D' e1 d' , transp D e2 d))))

EqJump2 : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
          → (p : Poly ℓ κ) (q : Poly ℓ' κ')
          → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
          → (f : p ⇆ q)
          → (g g' : (p ◃ r) ⇆ (s ◃ q))
          → EqJump1 p q r s g g'
          → Jump p q r s f g → Jump p q r s f g'
          → Set (ℓ ⊔ ℓ' ⊔ ℓ'' ⊔ κ ⊔ κ' ⊔ κ''')
EqJump2 (A , B) (C , D) (A' , B') (C' , D') (f , f♯)
        (g , g♯) (g' , g'♯) ej (e , e♯) (e' , e'♯) =
    (a : A) (h : B a → A') (d' : D' (fst (g (a , h)))) →
    let (e1 , ej2) = ej a h in
    let (e2 , ej3) = ej2 d' in
    Σ ((e2 • (e' a h (transp D' e1 d'))) ≡ e a h d')
      (λ e5 → (d : D (snd (g (a , h)) d'))
              → ((fst (ej3 d)) • ((e'♯ a h (transp D' e1 d') (transp D e2 d)) • (ap (f♯ a) ((transpComp e2 (e' a h (transp D' e1 d')) d) • (ap (λ ee → transp D ee d) e5))))) ≡ e♯ a h d' d)
```

Some key operations on Jump morphisms are as follows:

Given a jump morphism $j : r \xleftarrow{p \xrightarrow{f} q} s$ together with lenses $g : p' \leftrightarrows p$ and $h : q \leftrightarrows q'$ and $k : r' \leftrightarrows r$ and $l : s \leftrightarrows s'$, we obtain the structure of a Jump morphism $r' \xleftarrow{p' \xrightarrow{h \circ f \circ g} q'} s'$ on the composite $$
p' \triangleleft r' \xrightarrow{g ◃ k} p \triangleleft r \xrightarrow{j} s \triangleleft q \xrightarrow{l \triangleleft h} s' \triangleleft q'
$$ as follows:

```agda
transpLens : ∀ {ℓ ℓ' κ κ'} {A : Type ℓ} {A' : Type ℓ'} 
              (B : A → Type κ) (B' : A' → Type κ')
            → (f : A → A') (g : (x : A) → B' (f x) → B x) 
            → {a a' : A} {b : B' (f a)} (e : a ≡ a')
            → transp B e (g a b) ≡ g a' (transp B' (ap f e) b)
transpLens B B' f g refl = refl

JumpLens1 : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 ℓ7
               κ0 κ1 κ2 κ3 κ4 κ5 κ6 κ7}
            → (p : Poly ℓ0 κ0) (p' : Poly ℓ4 κ4)
            → (q : Poly ℓ1 κ1) (q' : Poly ℓ5 κ5)
            → (r : Poly ℓ2 κ2) (r' : Poly ℓ6 κ6)
            → (s : Poly ℓ3 κ3) (s' : Poly ℓ7 κ7)
            → (f : p ⇆ q) (j : (p ◃ r) ⇆ (s ◃ q))
            → (g : p' ⇆ p) (h : q ⇆ q') (k : r' ⇆ r) (l : s ⇆ s')
            → (p' ◃ r') ⇆ (s' ◃ q')
JumpLens1 p p' q q' r r' s s' f j g h k l =
    (comp (p' ◃ r') (p ◃ r) (s' ◃ q')
          (◃Lens p' p r' r g k)
          (comp (p ◃ r) (s ◃ q) (s' ◃ q')
                j (◃Lens s s' q q' l h)))

JumpLens2 : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 ℓ7
               κ0 κ1 κ2 κ3 κ4 κ5 κ6 κ7}
            → (p : Poly ℓ0 κ0) (p' : Poly ℓ4 κ4)
            → (q : Poly ℓ1 κ1) (q' : Poly ℓ5 κ5)
            → (r : Poly ℓ2 κ2) (r' : Poly ℓ6 κ6)
            → (s : Poly ℓ3 κ3) (s' : Poly ℓ7 κ7)
            → (f : p ⇆ q) (j : (p ◃ r) ⇆ (s ◃ q)) (jj : Jump p q r s f j)
            → (g : p' ⇆ p) (h : q ⇆ q') (k : r' ⇆ r) (l : s ⇆ s')
            → Jump p' q' r' s'
                  (comp p' p q' g
                        (comp p q q' f h))
                  (JumpLens1 p p' q q' r r' s s' f j g h k l)
JumpLens2 p p' q q' r r' s s' 
          (f , f♯) (j , j♯) (jj , jj♯) 
          (g , g♯) (h , h♯) (k , k♯) (l , l♯) =
    ( (λ a γ d' → ap h (jj (g a) (λ x → k (γ (g♯ a x))) (l♯ (fst (j ((g a) , (λ x → k (γ (g♯ a x)))))) d'))) 
    , λ a γ d' d → ap (g♯ a) ((jj♯ (g a) (λ x → k (γ (g♯ a x))) (l♯ (fst (j ((g a) , (λ x → k (γ (g♯ a x)))))) d') (h♯ (snd (j ((g a) , (λ x → k (γ (g♯ a x))))) (l♯ (fst (j ((g a) , (λ x → k (γ (g♯ a x)))))) d')) d)) • ap (f♯ (g a)) (transpLens (snd q) (snd q') h h♯ (jj (g a) (λ x → k (γ (g♯ a x))) (l♯ (fst (j ((g a) , (λ x → k (γ (g♯ a x)))))) d')))) )
```

Similarly, there are two distinct ways of composing jump morphisms: 

1. Given jump morphisms $j1 : s \xleftarrow{p \xleftarrow{f} q} t$ and $j2 : u \xleftarrow{q \xrightarrow{g} r} v$, we obtain a Jump structure $s \triangleleft u \xleftarrow{p \xrightarrow{g \circ f} r} t \triangleleft v$ on the composite $$
p ◃ (s \triangleleft u) \simeq (p \triangleleft s) \triangleleft u \xrightarrow{j1 \triangleleft u} (t \triangleleft q) \triangleleft u \simeq t \traingleleft (q \triangleleft u) \xrightarrow{j2} t \triangleleft (v \triangleleft r) \simeq (t \triangleleft v) \triangleleft r
$$
2. Given jump morphisms $j1 : t \xleftarrow{p \xrightarrow{f} q} u$ and $j2 : s \xleftarrow{r \xrightarrow{g} s} t$, we obtain a jump structure $s \xleftarrow{p \triangleleft r \xrightarrow{f \triangleleft g} q \triangleleft s} u$ on the composite $$
(p \triangleleft r) \triangleleft s \simeq p \triangleleft (r \triangleleft s) \xrightarrow{p \triangleleft j2} p \triangleleft (t \triangleleft s) \simeq (p \triangleleft t) \triangleleft s \xrightarrow{j1} (u \triangleleft q) \triangleleft s \simeq u \triangleleft (q \triangleleft s)
$$

Which are defined as follows:

```agda
JumpComp∘ : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 κ0 κ1 κ2 κ3 κ4 κ5 κ6}
            → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
            → (s : Poly ℓ3 κ3) (t : Poly ℓ4 κ4) 
            → (u : Poly ℓ5 κ5) (v : Poly ℓ6 κ6)
            → (p ◃ s) ⇆ (t ◃ q) → (q ◃ u) ⇆ (v ◃ r)
            → (p ◃ (s ◃ u)) ⇆ ((t ◃ v) ◃ r)
JumpComp∘ p q r s t u v h k =
    comp (p ◃ (s ◃ u)) ((p ◃ s) ◃ u) ((t ◃ v) ◃ r) 
         (◃assoc⁻¹ p s u) 
         (comp ((p ◃ s) ◃ u) ((t ◃ q) ◃ u) ((t ◃ v) ◃ r) 
               (◃Lens (p ◃ s) (t ◃ q) u u h (id u)) 
               (comp ((t ◃ q) ◃ u) (t ◃ (q ◃ u)) ((t ◃ v) ◃ r) 
                     (◃assoc t q u) 
                     (comp (t ◃ (q ◃ u)) (t ◃ (v ◃ r)) ((t ◃ v) ◃ r) 
                           (◃Lens t t (q ◃ u) (v ◃ r) (id t) k) 
                           (◃assoc⁻¹ t v r))))

JumpComp◃ : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 κ0 κ1 κ2 κ3 κ4 κ5 κ6}
            → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) 
            → (r : Poly ℓ2 κ2) (s : Poly ℓ3 κ3) 
            → (t : Poly ℓ4 κ4) (u : Poly ℓ5 κ5) (v : Poly ℓ6 κ6)
            → (r ◃ t) ⇆ (u ◃ s) → (p ◃ u) ⇆ (v ◃ q)
            → ((p ◃ r) ◃ t) ⇆ (v ◃ (q ◃ s))
JumpComp◃ p q r s t u v h k =
    comp ((p ◃ r) ◃ t) (p ◃ (r ◃ t)) (v ◃ (q ◃ s)) 
         (◃assoc p r t) 
         (comp (p ◃ (r ◃ t)) (p ◃ (u ◃ s)) (v ◃ (q ◃ s)) 
               (◃Lens p p (r ◃ t) (u ◃ s) (id p) h) 
               (comp (p ◃ (u ◃ s)) ((p ◃ u) ◃ s) (v ◃ (q ◃ s)) 
               (◃assoc⁻¹ p u s) 
               (comp ((p ◃ u) ◃ s) ((v ◃ q) ◃ s) (v ◃ (q ◃ s)) 
                     (◃Lens (p ◃ u) (v ◃ q) s s k (id s)) 
                     (◃assoc v q s))))
```

Upon inspection, one sees that the operations defined on jump morphisms above are just the same as those that figure in the constituent diagrams of a distributive law. E.g. given a polynomial universe `𝔲` equipped with Cartesian morphisms `σ : 𝔲 ◃ 𝔲 ⇆ 𝔲` and `π : 𝔲 ⇈ 𝔲 ⇆ 𝔲` in order for the morphism `distrLaw? 𝔲 π` defined above to be a distributive law, the following diagrams must commute:

It follows that, since $distrLaw? 𝔲 π$ is canonically equipped with the structure of a jump morphism, so are all composite morphisms appearing in these diagrams. One then wonders, perhaps, if there is some way in which the structure of a polynomial universe forces these diagrams (and all higher diagrams involving them) to commute, as was the case for the structure of the $\infty$-monad generated by $σ$. In fact, this question leads directly to the central theorem of this section, by which we shall be able to answer it in the affirmative – there is an equivalence between Jump morphisms $r \xleftarrow{p \xrightarrow{f} q} s$ and lenses $p ~{\upuparrows}[f] ~ r \leftrightarrows s$.

To convert lenses out of `_⇈[_][_]_` into jump morphisms, we may straightforwardly generalize the construction of `distrLaw?` given previously:

```agda
⇈→Jump1 : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
           → (p : Poly ℓ κ) (q : Poly ℓ' κ')
           → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
           → (f : p ⇆ q)
           → (p ⇈[ q ][ f ] r) ⇆ s
           → (p ◃ r) ⇆ (s ◃ q)
⇈→Jump1 p q r s (f , f♯) (g , g♯) =
    ( (λ (a , h) → g (a , h) , λ d' → f a) 
    , λ (a , h) (d' , d)
        → f♯ a d , g♯ (a , h) d' d)

⇈→Jump2 : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
           → (p : Poly ℓ κ) (q : Poly ℓ' κ')
           → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
           → (f : p ⇆ q)
           → (g : (p ⇈[ q ][ f ] r) ⇆ s)
           → Jump p q r s f (⇈→Jump1 p q r s f g)
⇈→Jump2 p q r s (f , f♯) (g , g♯) = 
    ( (λ a h d' → refl) 
    , (λ a h d' d → refl) )
```

Conversely, to convert Jump morphisms into lenses of the above form, we may proceed as below:

```agda
Jump→⇈ : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
           → (p : Poly ℓ κ) (q : Poly ℓ' κ')
           → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
           → (f : p ⇆ q)
           → (g : (p ◃ r) ⇆ (s ◃ q)) 
           → Jump p q r s f g
           → (p ⇈[ q ][ f ] r) ⇆ s
Jump→⇈ p q r s (f , f♯) (g , g♯) (e , e♯) =
    ( (λ (a , h) → fst (g (a , h))) 
    , λ (a , h) d' d 
      → transp (λ x → snd r (h x))
               (fst (g♯ (a , h) (d' , transp (snd q) (sym (e a h d')) d)) 
                     ≡〈 e♯ a h d' (transp (snd q) (sym (e a h d')) d) 〉 
                     ap (f♯ a) (symr (e a h d') d))
               (snd (g♯ (a , h) (d' , transp (snd q) (sym (e a h d')) d))) )
```

The proof that these two constructions are mutually inverse is then as follows:

```agda
⇈→Jumpl : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
           → (p : Poly ℓ κ) (q : Poly ℓ' κ')
           → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
           → (f : p ⇆ q)
           → (g : (p ⇈[ q ][ f ] r) ⇆ s)
           → EqLens (p ⇈[ q ][ f ] r) s 
                    (Jump→⇈ p q r s f 
                            (⇈→Jump1 p q r s f g)
                            (⇈→Jump2 p q r s f g))
                    g
⇈→Jumpl p q r s (f , f♯) (g , g♯) (a , h) =
    ( refl , (λ d' → refl) )

⇈→Jumpr1 : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
           → (p : Poly ℓ κ) (q : Poly ℓ' κ')
           → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
           → (f : p ⇆ q)
           → (g : (p ◃ r) ⇆ (s ◃ q))
           → (j : Jump p q r s f g)
           → EqJump1 p q r s
                     (⇈→Jump1 p q r s f
                              (Jump→⇈ p q r s f g j)) 
                     g
⇈→Jumpr1 p q r s (f , f♯) (g , g♯) (e , e♯) a h =
    ( refl 
    , λ d' → 
        ( sym (e a h d') 
        , (λ d → 
             ( sym (e♯ a h d' (transp (snd q) (sym (e a h d')) d) • ap (f♯ a) (symr (e a h d') d))
             , syml ((e♯ a h d' (transp (snd q) (sym (e a h d')) d)) • (ap (f♯ a) (symr (e a h d') d))) (snd (g♯ ((a , h)) (d' , (transp (snd q) (sym (e a h d')) d))))) ) ) )

⇈→Jumpr2 : ∀ {ℓ ℓ' ℓ'' ℓ''' κ κ' κ'' κ'''}
           → (p : Poly ℓ κ) (q : Poly ℓ' κ')
           → (r : Poly ℓ'' κ'') (s : Poly ℓ''' κ''')
           → (f : p ⇆ q)
           → (g : (p ◃ r) ⇆ (s ◃ q))
           → (j : Jump p q r s f g)
           → EqJump2 p q r s f
                     (⇈→Jump1 p q r s f
                              (Jump→⇈ p q r s f g j)) 
                     g
                     (⇈→Jumpr1 p q r s f g j)
                     (⇈→Jump2 p q r s f (Jump→⇈ p q r s f g j))
                     j
⇈→Jumpr2 p q r s (f , f♯) (g , g♯) (e , e♯) a h d' =
    ( sym (≡siml (e a h d'))
    , λ d → ap (λ ee → (sym (e♯ a h d' (transp (snd q) (sym (e a h d')) d) • ap (f♯ a) (symr (e a h d') d)) • (e♯ a h d' (transp (snd q) (sym (e a h d')) d) • ap (f♯ a) ee))) (transpCompSymr (e a h d') d) • sym (≡siml ((e♯ a h d' (transp (snd q) (sym (e a h d')) d)) • (ap (f♯ a) (symr (e a h d') d)))) )
```

One can moreover see that this equivalence between lenses out of `_⇈[_][_]_` converts the various operations on jump morphisms considered above into constructions involving the structures of `_⇈[_][_]_` we considered previously.

Specifically, under this equivalence, composing a jump morphism with arbitrary lenses corresponds to applying the functorial action of `_⇈[_][_]_` in the following way:

```
⇈→JumpLens≡ : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 ℓ7
                 κ0 κ1 κ2 κ3 κ4 κ5 κ6 κ7}
              → (p : Poly ℓ0 κ0) (p' : Poly ℓ4 κ4)
              → (q : Poly ℓ1 κ1) (q' : Poly ℓ5 κ5)
              → (r : Poly ℓ2 κ2) (r' : Poly ℓ6 κ6)
              → (s : Poly ℓ3 κ3) (s' : Poly ℓ7 κ7)
              → (f : p ⇆ q) (j : (p ⇈[ q ][ f ] r) ⇆ s)
              → (g : p' ⇆ p) (h : q ⇆ q')
              → (k : r' ⇆ r) (l : s ⇆ s')
              → JumpLens1 p p' q q' r r' s s' f (⇈→Jump1 p q r s f j) g h k l
                ≡ ⇈→Jump1 p' q' r' s' 
                        (comp p' p q' g 
                              (comp p q q' f h)) 
                        (comp (p' ⇈[ q' ][ comp p' p q' g (comp p q q' f h) ] r') 
                              (p ⇈[ q ][ f ] r) s' 
                              (⇈[]Lens p' p q' q r' r (comp p' p q' g (comp p q q' f h)) f g h k (λ a → refl , (λ b → refl))) (comp (p ⇈[ q ][ f ] r) s s' j l))
⇈→JumpLens≡ p p' q q' r r' s s' f j g h k l = refl

```

Additionally, Composing two jump morphisms via `jumpComp∘` corresponds to precomposing their respective representations as lenses out of `⇈` with the map `⇈[]Distr` defined above.

```agda
⇈[]Comp∘ : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 κ0 κ1 κ2 κ3 κ4 κ5 κ6}
           → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
           → (s : Poly ℓ3 κ3) (t : Poly ℓ4 κ4) 
           → (u : Poly ℓ5 κ5) (v : Poly ℓ6 κ6)
           → (f : p ⇆ q) (g : q ⇆ r)
           → (p ⇈[ q ][ f ] s) ⇆ t → (q ⇈[ r ][ g ] u) ⇆ v
           → (p ⇈[ r ][ comp p q r f g ] (s ◃ u)) ⇆ (t ◃ v)
⇈[]Comp∘ p q r s t u v f g h k = 
     comp (p ⇈[ r ][ (comp p q r f g) ] (s ◃ u)) 
          ((p ⇈[ q ][ f ] s) ◃ (q ⇈[ r ][ g ] u)) 
          (t ◃ v) 
          (⇈[]Distr p q r s u f g) 
          (◃Lens (p ⇈[ q ][ f ] s) t 
                 (q ⇈[ r ][ g ] u) v 
                 h k)

⇈→JumpComp∘≡ :  ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 κ0 κ1 κ2 κ3 κ4 κ5 κ6}
                → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) (r : Poly ℓ2 κ2)
                → (s : Poly ℓ3 κ3) (t : Poly ℓ4 κ4) 
                → (u : Poly ℓ5 κ5) (v : Poly ℓ6 κ6)
                → (f : p ⇆ q) (g : q ⇆ r)
                → (h : (p ⇈[ q ][ f ] s) ⇆ t) (k : (q ⇈[ r ][ g ] u) ⇆ v)
                → (JumpComp∘ p q r s t u v 
                             (⇈→Jump1 p q s t f h) 
                             (⇈→Jump1 q r u v g k)) 
                  ≡ (⇈→Jump1 p r (s ◃ u) (t ◃ v) 
                             (comp p q r f g) 
                             (⇈[]Comp∘ p q r s t u v f g h k))
⇈→JumpComp∘≡ p q r s t u v f g h k = refl
```

Similarly, composing two jump morphisms via `jumpComp◃` corresponds to composing their representations as lenses out of `⇈` with the map `⇈[]Curry` defined above.

```agda
⇈Comp◃ : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 κ0 κ1 κ2 κ3 κ4 κ5 κ6}
         → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) 
         → (r : Poly ℓ2 κ2) (s : Poly ℓ3 κ3) 
         → (t : Poly ℓ4 κ4) (u : Poly ℓ5 κ5) (v : Poly ℓ6 κ6)
         → (f : p ⇆ q) (g : r ⇆ s)
         → (r ⇈[ s ][ g ] t) ⇆ u → (p ⇈[ q ][ f ] u) ⇆ v
         → ((p ◃ r) ⇈[ (q ◃ s) ][ (◃Lens p q r s f g) ] t) ⇆ v
⇈Comp◃ p q r s t u v f g h k =
    comp ((p ◃ r) ⇈[ (q ◃ s) ][ (◃Lens p q r s f g) ] t) 
         (p ⇈[ q ][ f ] (r ⇈[ s ][ g ] t)) v 
         (⇈[]Curry p q r s t f g) 
         (comp (p ⇈[ q ][ f ] (r ⇈[ s ][ g ] t)) 
               (p ⇈[ q ][ f ] u) v 
               (⇈[]Lens p p q q (r ⇈[ s ][ g ] t) u f f (id p) (id q) h (λ a → refl , (λ b → refl))) 
               k)

⇈JumpComp◃≡ : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 ℓ4 ℓ5 ℓ6 κ0 κ1 κ2 κ3 κ4 κ5 κ6}
              → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1) 
              → (r : Poly ℓ2 κ2) (s : Poly ℓ3 κ3) 
              → (t : Poly ℓ4 κ4) (u : Poly ℓ5 κ5) (v : Poly ℓ6 κ6)
              → (f : p ⇆ q) (g : r ⇆ s)
              → (h : (r ⇈[ s ][ g ] t) ⇆ u) (k : (p ⇈[ q ][ f ] u) ⇆ v)
              → (JumpComp◃ p q r s t u v 
                           (⇈→Jump1 r s t u g h) 
                           (⇈→Jump1 p q u v f k)) 
                ≡ (⇈→Jump1 (p ◃ r) (q ◃ s) t v 
                           (◃Lens p q r s f g) 
                           (⇈Comp◃ p q r s t u v f g h k))
⇈JumpComp◃≡ p q r s t u v f g h k = refl
```

Additionally...

We say that a jump morphism is *jumpwise Cartesian* if its corresponding lens out of `_⇈[_][_]_` is Cartesian. Since all of the structure defined above on `_⇈[_][_]_` restricts to Cartesian morphisms, it follows that the above operations on jump morphisms preserve the property of being jumpwise Cartesian. 

Hence it follows that, if `distrLaw? 𝔲 π` is jumpwise Cartesian -- which will be the case precisely if π is Cartesian -- so are all of the composite morphisms appearing in the diagrams that must commute in order for `distrLaw?` to be a true distributive law. Then if `𝔲` is a polynomial universe, it follows that all of the corresponding diagrams in terms of `π` commute, and so, therefore, must the original diagrams. Hence `distrLaw? 𝔲 π` is indeed a distributive law, as desired.

```agda
ap⇈→Jump : ∀ {ℓ0 ℓ1 ℓ2 ℓ3 κ0 κ1 κ2 κ3}
           → (p : Poly ℓ0 κ0) (q : Poly ℓ1 κ1)
           → (r : Poly ℓ2 κ2) (s : Poly ℓ3 κ3)
           → (f : p ⇆ q) (g g' : (p ⇈[ q ][ f ] r) ⇆ s)
           → EqLens (p ⇈[ q ][ f ] r) s g g'
           → EqJump1 p q r s (⇈→Jump1 p q r s f g) (⇈→Jump1 p q r s f g')
ap⇈→Jump p q r s f g g' e a γ = 
    ( (fst (e (a , γ))) 
    , (λ d' → ( refl 
              , (λ d → ( refl 
                       , coAp (snd (e (a , γ)) d') d )) )) )

distrLaw1Comp1 : ∀ {ℓ κ} (𝔲 : Poly ℓ κ)
                 → (σ : (𝔲 ◃ 𝔲) ⇆ 𝔲) (π : (𝔲 ⇈ 𝔲) ⇆ 𝔲)
                 → ((𝔲 ◃ 𝔲) ⇈[ 𝔲 ][ σ ] 𝔲) ⇆ 𝔲
distrLaw1Comp1 𝔲 σ π = 
    comp ((𝔲 ◃ 𝔲) ⇈[ 𝔲 ][ σ ] 𝔲) ((𝔲 ◃ 𝔲) ⇈ 𝔲) 𝔲 
         (⇈[]Lens (𝔲 ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲 (𝔲 ◃ 𝔲) 𝔲 𝔲 σ (id (𝔲 ◃ 𝔲)) (id (𝔲 ◃ 𝔲)) σ (id 𝔲) (λ a → refl , (λ b → refl))) 
         (⇈Comp◃ 𝔲 𝔲 𝔲 𝔲 𝔲 𝔲 𝔲 (id 𝔲) (id 𝔲) π π)

distrLaw1Comp2 : ∀ {ℓ κ} (𝔲 : Poly ℓ κ)
                 → (σ : (𝔲 ◃ 𝔲) ⇆ 𝔲) (π : (𝔲 ⇈ 𝔲) ⇆ 𝔲)
                 → ((𝔲 ◃ 𝔲) ⇈[ 𝔲 ][ σ ] 𝔲) ⇆ 𝔲
distrLaw1Comp2 𝔲 σ π = 
    comp ((𝔲 ◃ 𝔲) ⇈[ 𝔲 ][ σ ] 𝔲) (𝔲 ⇈ 𝔲) 𝔲 
         (⇈[]Lens (𝔲 ◃ 𝔲) 𝔲 𝔲 𝔲 𝔲 𝔲 σ (id 𝔲) σ (id 𝔲) (id 𝔲) (λ a → refl , (λ b → refl))) π

{- distrLaw1 : ∀ {ℓ κ} (𝔲 : Poly ℓ κ) → isSubterminal 𝔲
            → (σ : (𝔲 ◃ 𝔲) ⇆ 𝔲) → isCartesian (𝔲 ◃ 𝔲) 𝔲 σ
            → (π : (𝔲 ⇈ 𝔲) ⇆ 𝔲) → isCartesian (𝔲 ⇈ 𝔲) 𝔲 π
            → EqJump1 (𝔲 ◃ 𝔲) 𝔲 𝔲 𝔲
              (JumpLens1 (𝔲 ◃ 𝔲) (𝔲 ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲 𝔲 𝔲 𝔲 𝔲 (id (𝔲 ◃ 𝔲)) (JumpComp◃ 𝔲 𝔲 𝔲 𝔲 𝔲 𝔲 𝔲 (distrLaw? 𝔲 π) (distrLaw? 𝔲 π)) (id (𝔲 ◃ 𝔲)) σ (id 𝔲) (id 𝔲))
              (JumpLens1 𝔲 (𝔲 ◃ 𝔲) 𝔲 𝔲 𝔲 𝔲 𝔲 𝔲 (id 𝔲) (distrLaw? 𝔲 π) σ (id 𝔲) (id 𝔲) (id 𝔲))
distrLaw1 𝔲 su σ cσ π cπ = ap⇈→Jump (𝔲 ◃ 𝔲) 𝔲 𝔲 𝔲 σ 
                           (distrLaw1Comp1 𝔲 σ π) 
                           (distrLaw1Comp2 𝔲 σ π)
                           (su ((𝔲 ◃ 𝔲) ⇈[ 𝔲 ][ σ ] 𝔲) 
                               (distrLaw1Comp1 𝔲 σ π) 
                               (distrLaw1Comp2 𝔲 σ π) 
                               (compCartesian ((𝔲 ◃ 𝔲) ⇈[ 𝔲 ][ σ ] 𝔲) ((𝔲 ◃ 𝔲) ⇈ 𝔲) 𝔲 
                                              (⇈[]Lens (𝔲 ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲 (𝔲 ◃ 𝔲) 𝔲 𝔲 σ (id (𝔲 ◃ 𝔲)) (id (𝔲 ◃ 𝔲)) σ (id 𝔲) (λ a → refl , (λ b → refl))) 
                                              (⇈Comp◃ 𝔲 𝔲 𝔲 𝔲 𝔲 𝔲 𝔲 (id 𝔲) (id 𝔲) π π) 
                                              (⇈[]LensCart (𝔲 ◃ 𝔲) (𝔲 ◃ 𝔲) 𝔲 (𝔲 ◃ 𝔲) 𝔲 𝔲 σ (id (𝔲 ◃ 𝔲)) (id (𝔲 ◃ 𝔲)) σ (id 𝔲) cσ (idCart 𝔲) (λ a → refl , (λ b → refl))) 
                                              {!   !}) 
                               {!   !}) -}
```