theory Flatinduct
  imports Complex_Main
begin
consts P1 :: "nat ⇒ bool" P2 :: "nat ⇒ bool"

section \<open>Defining testing functions\<close>

fun f' where
  "f' (Suc (Suc x)) = (if P1 x then f' (Suc x) else if P2 x then f' x else f' 0)"
thm f'.induct[of P n]


(* Test: The negation term can never occur here. Maybe try constructing a proof to False from the negation term and
 * do not add it if the proof succeeds? *)
lemma f_induct: "⟦⋀x. ⟦P1 x; P (Suc x)⟧ ⟹ P (Suc (Suc x));
       ⋀x. ⟦¬P1 x; P2 x; P x⟧ ⟹ P (Suc (Suc x));
       ⋀x. ⟦¬P1 x; ¬ P2 x; P 0⟧ ⟹ P (Suc (Suc x));
  P 0; P (Suc 0)⟧
⟹ P a"
by (metis f'.induct)

lemma f'_induct_exhaustive: "\<And>x. \<lbrakk> ⟦P1 x⟧ \<Longrightarrow> False;  ⟦¬P1 x; P2 x⟧ \<Longrightarrow> False;  ⟦¬P1 x; ¬ P2 x⟧ \<Longrightarrow> False\<rbrakk> \<Longrightarrow> False"
  by blast (* Here it can be proved. *)

fun g :: "nat ⇒ nat" where
"g n = (case n of 0 ⇒ 0 | Suc 0 ⇒ g 0 | Suc (Suc n) ⇒ g n)"
thm g.induct

lemma g_induct: "⟦
  (⋀n. \<lbrakk>⋀nat. n=Suc nat \<Longrightarrow> nat=0 \<Longrightarrow> False; ⋀nat nata. n = Suc nat \<Longrightarrow> nat = Suc nata \<Longrightarrow> False\<rbrakk> ⟹ P n);
  (⋀n. ⋀nat.      ⟦n = Suc nat; nat = 0; P 0          ⟧ ⟹ P n);
  (⋀n. ⋀nat nata. ⟦n = Suc nat; nat = Suc nata; P nata⟧ ⟹ P n)⟧
⟹ P a"
by (metis g.induct)

lemma g_induct_exhaustive: "(⋀n. \<lbrakk>⋀nat. n=Suc nat \<Longrightarrow> nat=0 \<Longrightarrow> False; ⋀nat nata. n = Suc nat \<Longrightarrow> nat = Suc nata \<Longrightarrow> False\<rbrakk> ⟹ P n)"
  oops (* Here it can't be proved => Rule is needed *)

fun h :: "nat \<Rightarrow> nat" where
  \<open>h 0 = 0\<close> |
  \<open>h (Suc n) = (case n of 0 \<Rightarrow> h n | Suc n \<Rightarrow> h n)\<close>
thm h.induct[of P x]

lemma h_induct: "P 0 \<Longrightarrow>
 (\<And>n. n = 0 \<Longrightarrow> P n \<Longrightarrow> P (Suc n)) \<Longrightarrow>
 (\<And>n nat. n = Suc nat \<Longrightarrow> P nat \<Longrightarrow> P (Suc n)) \<Longrightarrow>
 (\<And>n. (n = 0 \<Longrightarrow> False) \<Longrightarrow> (\<And>nat. n = Suc nat \<Longrightarrow> False) \<Longrightarrow> P (Suc n)) \<Longrightarrow>
 P n"
by (rule h.induct) (metis (no_types))+

fun i :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  \<open>i n m = (case (n, m) of (0, Suc 0) \<Rightarrow> i 0 0 | (Suc k, Suc l) \<Rightarrow> i k l | _ \<Rightarrow> False)\<close>
thm i.induct

lemma i_induct: "(\<And>n m. (\<And>x y nat.
      (x, y) = (n, m) \<Longrightarrow> x = 0 \<Longrightarrow> y = Suc nat \<Longrightarrow> nat = 0 \<Longrightarrow> P 0 0) \<Longrightarrow>
     (\<And>x y nat nata.
      (x, y) = (n, m) \<Longrightarrow> x = Suc nat \<Longrightarrow> y = Suc nata \<Longrightarrow> P nat nata) \<Longrightarrow>
     P n m) \<Longrightarrow>
 P n m"
  by (rule i.induct[of P]) (metis (no_types))+ (* no_types makes proof way faster *)
  (* also, this theorem is not provable by (metis i.induct), so the procedure can't rely on that *)


section \<open>README example\<close>

fun f where
"f 0 = 0" |
"f (Suc n) = (if n = 1 then f 1 else f n)"
thm f'.induct[of P any] (* ugly *)


ML_file \<open>flatinduct.ML\<close>

thm f.induct[flatinduct, of P any] (* tadaaa *)

thm f.induct[flatinduct] (* basic test cases *)
    g.induct[flatinduct]
    h.induct[flatinduct]
    i.induct[flatinduct]

(* TODO: Testing *)
(* suggestion: check which metis call is best suited *)
(* use speccheck for testing *)
(* find_theorems name:".induct" *)


end
