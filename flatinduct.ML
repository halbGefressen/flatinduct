(* Author: Christian Zimmerer *)
signature FLATCASES =
sig
  val flatinduct : Proof.context -> Thm.thm -> Thm.thm
end;

structure Flatcasese : FLATCASES =
struct

fun metis_default_tac ctxt = (Metis_Tactic.metis_tac [ATP_Proof_Reconstruct.no_type_enc]
                                     ATP_Problem_Generate.combsN ctxt [] 1)

fun is_P (Const ("HOL.Trueprop", propsig ) $ (bprop  $ _))
         (Const ("HOL.Trueprop", propsig') $ (bprop' $ _))
        = propsig = propsig' andalso bprop = bprop'
  | is_P _ _ = false

fun is_split_induct_case concl t =
  let val (vars, body) = (strip_all_vars t, strip_all_body t)
  in not (List.null vars) andalso
    let val (preconds, subconcl) = Logic.strip_horn body
    in preconds |> not o null andalso subconcl |> is_P concl
         andalso preconds |> List.all (strip_all_body #> Logic.strip_imp_concl #> is_P concl)
    end
  end

(* TODO: make it single pass *)
fun transform_split_induct_case ctxt t =
  let val horn as (vars, (preconds, subconcl)) = (strip_all_vars t, strip_all_body t) ||> Logic.strip_horn
      val flatten = (fn x =>
            let val (pvars, (ppre, psub)) = (x |> strip_all_vars, x |> strip_all_body) ||> Logic.strip_horn
            in (vars, (pvars, (ppre @ [psub], subconcl) ||> incr_boundvars (length pvars))
               ||> Logic.list_implies |> Logic.list_all) |> Logic.list_all
            end)
      val negator = (fn x => (strip_all_vars x, strip_all_body x))
                             ##> (Logic.strip_horn ##> K @{term "Trueprop False"})
                             ##> Logic.list_implies #> Logic.list_all
      (* check with simplifier if the negated condition can occur *)
      val omit_catchall = (Timeout.apply (Time.fromSeconds 3) (K true)
                            (Goal.prove ctxt [] []
                               ((vars, (map negator preconds, @{term "Trueprop False"}))
                                 ||> Logic.list_implies |> Logic.list_all)
                               (K (metis_default_tac ctxt)))
                             handle ERROR _ => false)
                           handle Time.Time => false
      val cons_catchall = if omit_catchall then I
                            else horn ||> (I #>> map negator #> Logic.list_implies)
                                   |> Logic.list_all |> curry (op ::)
  in map flatten preconds |> cons_catchall
  end

fun flatinduct_rewrite ctxt t =
  let val horn as (_, concl) = (Logic.strip_horn o Thm.prop_of) t
      val rewrite_splits = map (fn tn => if is_split_induct_case concl tn
                                  then transform_split_induct_case ctxt tn else [tn])
  in horn |>> rewrite_splits |>> List.concat |> Logic.list_implies
  end

fun flatinduct ctxt t =
  let val ((vars, t), ctxt') = (Variable.import true [t] ctxt) |>> (I ##> hd)
      val tactic = (fn _ => (* by (rule t) (metis (no_types))+ *)
        (resolve_tac ctxt' [Thm.instantiate vars t] 1) THEN
         REPEAT (metis_default_tac ctxt'))
      val proven = Goal.prove ctxt [] [] (flatinduct_rewrite ctxt t) tactic
  in singleton (Variable.export ctxt' ctxt) proven
  end

val _ = Theory.setup (Attrib.setup \<^binding>\<open>flatinduct\<close>
  (Scan.succeed (Thm.rule_attribute [] (flatinduct o Context.proof_of)))
    "pulls the case splits in induction rules to the top level")

end;
