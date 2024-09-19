(* Author: Christian Zimmerer *)
signature FLATINDUCT =
sig
  val flatinduct : Proof.context -> Thm.thm -> Thm.thm
end;

structure Flatinduct : FLATINDUCT =
struct

(* Shorthand for (metis (no_types)). *)
fun metis_default_tac ctxt = (Metis_Tactic.metis_tac [ATP_Proof_Reconstruct.no_type_enc]
                                     ATP_Problem_Generate.combsN ctxt [] 1)

(* Simple pattern equality check for predicates. *)
fun is_P t1 t2 =
  let val relevant_terms = strip_comb ##> hd ##> head_of
  in (relevant_terms t1 = relevant_terms t2) handle Empty => false
  end 

(* Checks if a thrm was probably generated from a case distinction. Basically a pattern match. *)
fun is_split_induct_case concl t =
  let val (vars, body) = (strip_all_vars t, strip_all_body t)
  in not (List.null vars) andalso
    let val (preconds, subconcl) = Logic.strip_horn body
    in preconds |> not o null andalso subconcl |> is_P concl
         andalso preconds |> List.all (strip_all_body #> Logic.strip_imp_concl #> is_P concl)
    end
  end

(* Rewrites a single constructor pattern containing a split pattern (hard assumption!).
 * Step 1: Strip the quantors and split off the subgoal from the conclusions.
 * Step 2: Imply the subgoal for each subpremise (again, inside its quantors).
 * Step 3: If the subpremises do not cover all cases explicitly, create an extra case that covers the case where
 *           none of the premises hold and show that the subgoal holds anyway. (for "case _ of _" patterns)
 * Step 4: Put it all back together.
 * *)
(* TODO: make it single pass *)
fun transform_split_induct_case ctxt t =
  let val horn as (vars, (preconds, subconcl)) = (* Step 1 *)
        (strip_all_vars t, strip_all_body t) ||> Logic.strip_horn
      (* Step 2 *)
      val flatten = (fn x =>
            let val (pvars, (ppre, psub)) = (x |> strip_all_vars, x |> strip_all_body) ||> Logic.strip_horn
            in (vars, (pvars, (ppre @ [psub], subconcl) ||> incr_boundvars (length pvars))
               ||> Logic.list_implies |> Logic.list_all) |> Logic.list_all
            end)
      (* Step 3 *)
      val negator = (fn x => (strip_all_vars x, strip_all_body x))
                             ##> (Logic.strip_horn ##> K @{term "Trueprop False"})
                             ##> Logic.list_implies #> Logic.list_all
      (* check if the negated condition can occur *)
      val omit_catchall = (Timeout.apply (Time.fromSeconds 3) (K true)
                            (Goal.prove ctxt [] []
                               ((vars, (map negator preconds, @{term "Trueprop False"}))
                                 ||> Logic.list_implies |> Logic.list_all)
                               (K (metis_default_tac ctxt)))
                             handle ERROR _ => false) (* haven't found a better way :< *)
                           handle Time.Time => false
      (* Conditional append: Either apply identity or "function prepending the case to list" *)
      val cons_catchall = if omit_catchall then I
                            else horn ||> (I #>> map negator #> Logic.list_implies)
                                   |> Logic.list_all |> curry (op ::)
  in map flatten preconds |> cons_catchall (* Step 4 *)
  end


(* Rewrites a thrm to flatten split patterns in induction rules. *)
fun flatinduct_rewrite ctxt t =
  let val horn as (_, concl) = (Logic.strip_horn o Thm.prop_of) t
      val rewrite_splits = map (fn tn => if is_split_induct_case concl tn
                                  then transform_split_induct_case ctxt tn else [tn])
  in horn |>> rewrite_splits |>> List.concat |> Logic.list_implies
  end

(* Generates and proves the flattened form of the specified induction rule. *)
fun flatinduct ctxt t =
  let val ((vars, t), ctxt') = (Variable.import true [t] ctxt) |>> (I ##> hd)
      val tactic = (fn _ => (* by (rule t) (metis (no_types))+ *)
        (resolve_tac ctxt' [Thm.instantiate vars t] 1) THEN
         REPEAT (SMT_Solver.smt_tac ctxt' [] 1))
      val proven = Goal.prove ctxt [] [] (flatinduct_rewrite ctxt t) tactic
  in singleton (Variable.export ctxt' ctxt) proven
  end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>flatinduct\<close>
  (Scan.succeed (Thm.rule_attribute [] (flatinduct o Context.proof_of)))
    "pulls the case splits in induction rules to the top level")

end;
