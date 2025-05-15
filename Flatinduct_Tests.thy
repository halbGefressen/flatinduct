theory Flatinduct_Tests
  imports "HOL-Library.Tree" "HOL-Library.Countable" "HOL-Library.FSet" "HOLCF.ConvexPD"
begin

ML_file \<open>flatinduct.ML\<close>

find_theorems (10000) name: ".induct" -name: ".induct_"

ML \<open>
val x = Specification.theorem_cmd
  \<close>

termination

(*  metis cannot solve this alone
lemma problem: "
P 0 \<Longrightarrow>
(\<And>n. (\<And>a aa. sum_decode n = Inl a \<Longrightarrow> sum_decode a = Inl aa \<Longrightarrow> P aa) \<Longrightarrow>
  (\<And>a b. sum_decode n = Inl a \<Longrightarrow> sum_decode a = Inr b \<Longrightarrow> P b) \<Longrightarrow>
  (\<And>b ba x y. sum_decode n = Inr b \<Longrightarrow> sum_decode b = Inr ba \<Longrightarrow> (x, y) = prod_decode ba \<Longrightarrow> P x) \<Longrightarrow>
  (\<And>b ba x y. sum_decode n = Inr b \<Longrightarrow> sum_decode b = Inr ba \<Longrightarrow> (x, y) = prod_decode ba \<Longrightarrow> P y) \<Longrightarrow> P (Suc n)) \<Longrightarrow>
P x" by (simp add: Countable.nth_item.induct[of P x])

ML \<open>
Syntax.pretty_term @{context} (Flatinduct.flatinduct_rewrite @{context} @{thm problem})
  \<close>

lemma "P 0 \<Longrightarrow>
    (\<And>n. (\<And>a aa. sum_decode n = Inl a \<Longrightarrow> sum_decode a = Inl aa \<Longrightarrow> False) \<Longrightarrow>
      (\<And>a b. sum_decode n = Inl a \<Longrightarrow> sum_decode a = Inr b \<Longrightarrow> False) \<Longrightarrow>
      (\<And>b ba x y. sum_decode n = Inr b \<Longrightarrow> sum_decode b = Inr ba \<Longrightarrow> (x, y) = prod_decode ba \<Longrightarrow> False) \<Longrightarrow>
      (\<And>b ba x y. sum_decode n = Inr b \<Longrightarrow> sum_decode b = Inr ba \<Longrightarrow> (x, y) = prod_decode ba \<Longrightarrow> False) \<Longrightarrow> P (Suc n)) \<Longrightarrow>
    (\<And>n a aa. sum_decode n = Inl a \<Longrightarrow> sum_decode a = Inl aa \<Longrightarrow> P aa \<Longrightarrow> P (Suc n)) \<Longrightarrow>
    (\<And>n a b. sum_decode n = Inl a \<Longrightarrow> sum_decode a = Inr b \<Longrightarrow> P b \<Longrightarrow> P (Suc n)) \<Longrightarrow>
    (\<And>n b ba x y. sum_decode n = Inr b \<Longrightarrow> sum_decode b = Inr ba \<Longrightarrow> (x, y) = prod_decode ba \<Longrightarrow> P x \<Longrightarrow> P (Suc n)) \<Longrightarrow>
    (\<And>n b ba x y. sum_decode n = Inr b \<Longrightarrow> sum_decode b = Inr ba \<Longrightarrow> (x, y) = prod_decode ba \<Longrightarrow> P y \<Longrightarrow> P (Suc n)) \<Longrightarrow> P x"
  apply (rule Countable.nth_item.induct[of P])
    apply (metis Countable.nth_item.induct[of P])
    apply (smt Countable.nth_item.induct[of P])
      done
*)

thm Countable.nth_item.induct[of "P"]

declare [[metis_verbose=false]]

ML \<open>
(*fun gen_find_theorems filter ctxt opt_goal opt_limit rem_dups raw_criteria =*)
val (SOME count, results) = Find_Theorems.find_theorems @{context} NONE (SOME 100000) true [(true, Find_Theorems.Name ".induct"), (false, Find_Theorems.Name ".induct_")]

fun testFacts nil = nil
  | testFacts ((reference, t)::xs) = let
  val before = Time.now ()
  val inducted = (K true (Flatinduct.flatinduct 10 @{context} t)) handle Time.Time => false
  val after = Time.now ()
  val _ = writeln (if inducted then String.concat [Int.toString (Time.toMilliseconds (after - before)), "ms"] else String.concat ["timeout/err at", @{make_string} t])
  in inducted :: testFacts xs
  end
val result = testFacts results
val success = List.all I result
val resultLen = length result

val _ = Attrib.setup_config_bool
  \<close>

print_commands
end
