let str str =
  Feedback.msg_notice (Pp.str str)

let string_of_econstr env evd (t : EConstr.t) : string =
  let pp = Printer.pr_constr_env env evd (EConstr.to_constr evd t) in
  Pp.string_of_ppcmds pp

let econstr env evd t =
  string_of_econstr env evd t |> str

let econstr_debug evd t =
  t |> EConstr.to_constr evd |> Constr.debug_print |>
  Feedback.msg_notice
