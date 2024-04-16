(* Auto-generated from "logic.atd" *)
[@@@ocaml.warning "-27-32-33-35-39"]

type varenv = Fo_t.varenv

type uid = Logic_t.uid

type type_ = Fo_t.type_

type term = Fo_t.term

type sig_ = Fo_t.sig_

type pkind = Logic_t.pkind

type name = Fo_t.name

type logcon = Fo_t.logcon

type form = Fo_t.form

type hyp = Logic_t.hyp = { h_id: uid; h_form: form }

type lgoal = Logic_t.lgoal

type lenv = Fo_t.lenv

type lemma = Logic_t.lemma = { l_user: name; l_full: name; l_stmt: form }

type env = Fo_t.env

type lemmadb = Logic_t.lemmadb

type expr = Fo_t.expr

type choice = Logic_t.choice

type itrace = Logic_t.itrace

type ctxt = Logic_t.ctxt = { kind: pkind; handle: uid }

type ipath = Logic_t.ipath = { ctxt: ctxt; sub: int list }

type goal = Logic_t.goal = { g_env: env; g_hyps: hyp list; g_concl: form }

type goals = Logic_t.goals

type bvar = Fo_t.bvar

type bkind = Fo_t.bkind

type arity = Fo_t.arity

type aident = Logic_t.aident

type agoal = Logic_t.agoal = {
  a_vars: varenv;
  a_hyps: hyp list;
  a_concl: form
}

type action = Logic_t.action

let varenv_tag = Fo_b.varenv_tag
let write_untagged_varenv = (
  Fo_b.write_untagged_varenv
)
let write_varenv ob x =
  Bi_io.write_tag ob Fo_b.varenv_tag;
  write_untagged_varenv ob x
let string_of_varenv ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_varenv ob x;
  Bi_outbuf.contents ob
let get_varenv_reader = (
  Fo_b.get_varenv_reader
)
let read_varenv = (
  Fo_b.read_varenv
)
let varenv_of_string ?pos s =
  read_varenv (Bi_inbuf.from_string ?pos s)
let uid_tag = Bi_io.string_tag
let write_untagged_uid = (
  Bi_io.write_untagged_string
)
let write_uid ob x =
  Bi_io.write_tag ob Bi_io.string_tag;
  write_untagged_uid ob x
let string_of_uid ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_uid ob x;
  Bi_outbuf.contents ob
let get_uid_reader = (
  Atdgen_runtime.Ob_run.get_string_reader
)
let read_uid = (
  Atdgen_runtime.Ob_run.read_string
)
let uid_of_string ?pos s =
  read_uid (Bi_inbuf.from_string ?pos s)
let type__tag = Fo_b.type__tag
let write_untagged_type_ = (
  Fo_b.write_untagged_type_
)
let write_type_ ob x =
  Bi_io.write_tag ob Fo_b.type__tag;
  write_untagged_type_ ob x
let string_of_type_ ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_type_ ob x;
  Bi_outbuf.contents ob
let get_type__reader = (
  Fo_b.get_type__reader
)
let read_type_ = (
  Fo_b.read_type_
)
let type__of_string ?pos s =
  read_type_ (Bi_inbuf.from_string ?pos s)
let term_tag = Fo_b.term_tag
let write_untagged_term = (
  Fo_b.write_untagged_term
)
let write_term ob x =
  Bi_io.write_tag ob Fo_b.term_tag;
  write_untagged_term ob x
let string_of_term ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_term ob x;
  Bi_outbuf.contents ob
let get_term_reader = (
  Fo_b.get_term_reader
)
let read_term = (
  Fo_b.read_term
)
let term_of_string ?pos s =
  read_term (Bi_inbuf.from_string ?pos s)
let sig__tag = Fo_b.sig__tag
let write_untagged_sig_ = (
  Fo_b.write_untagged_sig_
)
let write_sig_ ob x =
  Bi_io.write_tag ob Fo_b.sig__tag;
  write_untagged_sig_ ob x
let string_of_sig_ ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_sig_ ob x;
  Bi_outbuf.contents ob
let get_sig__reader = (
  Fo_b.get_sig__reader
)
let read_sig_ = (
  Fo_b.read_sig_
)
let sig__of_string ?pos s =
  read_sig_ (Bi_inbuf.from_string ?pos s)
let pkind_tag = Bi_io.variant_tag
let write_untagged_pkind = (
  fun ob x ->
    match x with
      | `Hyp -> Bi_outbuf.add_char4 ob '\000' '7' '\012' '\031'
      | `Concl -> Bi_outbuf.add_char4 ob ']' '\139' '[' 'K'
      | `Var x ->
        Bi_outbuf.add_char4 ob '\128' 'A' '\150' '\199';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.variant_tag;
            match x with
              | `Head -> Bi_outbuf.add_char4 ob '/' '\228' 'U' '@'
              | `Body -> Bi_outbuf.add_char4 ob '+' '\244' '\166' '\194'
        ) ob x
)
let write_pkind ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_pkind ob x
let string_of_pkind ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_pkind ob x;
  Bi_outbuf.contents ob
let get_pkind_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 3607583, false -> `Hyp
            | -578069685, false -> `Concl
            | 4298439, true -> (`Var (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
                    Bi_io.read_hashtag ib (fun ib h has_arg ->
                      match h, has_arg with
                        | 803493184, false -> `Head
                        | 737453762, false -> `Body
                        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
                    )
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_pkind = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 3607583, false -> `Hyp
        | -578069685, false -> `Concl
        | 4298439, true -> (`Var (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
                Bi_io.read_hashtag ib (fun ib h has_arg ->
                  match h, has_arg with
                    | 803493184, false -> `Head
                    | 737453762, false -> `Body
                    | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
                )
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let pkind_of_string ?pos s =
  read_pkind (Bi_inbuf.from_string ?pos s)
let name_tag = Fo_b.name_tag
let write_untagged_name = (
  Fo_b.write_untagged_name
)
let write_name ob x =
  Bi_io.write_tag ob Fo_b.name_tag;
  write_untagged_name ob x
let string_of_name ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_name ob x;
  Bi_outbuf.contents ob
let get_name_reader = (
  Fo_b.get_name_reader
)
let read_name = (
  Fo_b.read_name
)
let name_of_string ?pos s =
  read_name (Bi_inbuf.from_string ?pos s)
let logcon_tag = Fo_b.logcon_tag
let write_untagged_logcon = (
  Fo_b.write_untagged_logcon
)
let write_logcon ob x =
  Bi_io.write_tag ob Fo_b.logcon_tag;
  write_untagged_logcon ob x
let string_of_logcon ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_logcon ob x;
  Bi_outbuf.contents ob
let get_logcon_reader = (
  Fo_b.get_logcon_reader
)
let read_logcon = (
  Fo_b.read_logcon
)
let logcon_of_string ?pos s =
  read_logcon (Bi_inbuf.from_string ?pos s)
let form_tag = Fo_b.form_tag
let write_untagged_form = (
  Fo_b.write_untagged_form
)
let write_form ob x =
  Bi_io.write_tag ob Fo_b.form_tag;
  write_untagged_form ob x
let string_of_form ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_form ob x;
  Bi_outbuf.contents ob
let get_form_reader = (
  Fo_b.get_form_reader
)
let read_form = (
  Fo_b.read_form
)
let form_of_string ?pos s =
  read_form (Bi_inbuf.from_string ?pos s)
let hyp_tag = Bi_io.record_tag
let write_untagged_hyp : Bi_outbuf.t -> hyp -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    Bi_outbuf.add_char4 ob '\197' '\006' '\162' '\146';
    (
      write_uid
    ) ob x.h_id;
    Bi_outbuf.add_char4 ob '\139' '\239' '\003' '\187';
    (
      write_form
    ) ob x.h_form;
)
let write_hyp ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_hyp ob x
let string_of_hyp ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_hyp ob x;
  Bi_outbuf.contents ob
let get_hyp_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_h_id = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_h_form = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | -989420910 ->
              field_h_id := (
                (
                  read_uid
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | 200213435 ->
              field_h_form := (
                (
                  read_form
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x3 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "h_id"; "h_form" |];
        (
          {
            h_id = !field_h_id;
            h_form = !field_h_form;
          }
         : hyp)
)
let read_hyp = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_h_id = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_h_form = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | -989420910 ->
          field_h_id := (
            (
              read_uid
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | 200213435 ->
          field_h_form := (
            (
              read_form
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x3 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "h_id"; "h_form" |];
    (
      {
        h_id = !field_h_id;
        h_form = !field_h_form;
      }
     : hyp)
)
let hyp_of_string ?pos s =
  read_hyp (Bi_inbuf.from_string ?pos s)
let _hyp_list_tag = Bi_io.array_tag
let write_untagged__hyp_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    hyp_tag
    (
      write_untagged_hyp
    )
)
let write__hyp_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__hyp_list ob x
let string_of__hyp_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__hyp_list ob x;
  Bi_outbuf.contents ob
let get__hyp_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_hyp_reader
  )
)
let read__hyp_list = (
  Atdgen_runtime.Ob_run.read_list (
    get_hyp_reader
  )
)
let _hyp_list_of_string ?pos s =
  read__hyp_list (Bi_inbuf.from_string ?pos s)
let lgoal_tag = Bi_io.tuple_tag
let write_untagged_lgoal = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        write__hyp_list
      ) ob x
    );
    (
      let _, x = x in (
        write_form
      ) ob x
    );
)
let write_lgoal ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_lgoal ob x
let string_of_lgoal ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_lgoal ob x;
  Bi_outbuf.contents ob
let get_lgoal_reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            read__hyp_list
          ) ib
        in
        let x1 =
          (
            read_form
          ) ib
        in
        for i = 2 to len - 1 do Bi_io.skip ib done;
        (x0, x1)
)
let read_lgoal = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        read__hyp_list
      ) ib
    in
    let x1 =
      (
        read_form
      ) ib
    in
    for i = 2 to len - 1 do Bi_io.skip ib done;
    (x0, x1)
)
let lgoal_of_string ?pos s =
  read_lgoal (Bi_inbuf.from_string ?pos s)
let lenv_tag = Fo_b.lenv_tag
let write_untagged_lenv = (
  Fo_b.write_untagged_lenv
)
let write_lenv ob x =
  Bi_io.write_tag ob Fo_b.lenv_tag;
  write_untagged_lenv ob x
let string_of_lenv ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_lenv ob x;
  Bi_outbuf.contents ob
let get_lenv_reader = (
  Fo_b.get_lenv_reader
)
let read_lenv = (
  Fo_b.read_lenv
)
let lenv_of_string ?pos s =
  read_lenv (Bi_inbuf.from_string ?pos s)
let lemma_tag = Bi_io.record_tag
let write_untagged_lemma : Bi_outbuf.t -> lemma -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 3;
    Bi_outbuf.add_char4 ob '\175' 'I' '\166' '>';
    (
      write_name
    ) ob x.l_user;
    Bi_outbuf.add_char4 ob '\165' '`' '\253' '\130';
    (
      write_name
    ) ob x.l_full;
    Bi_outbuf.add_char4 ob '\173' '\248' '\002' ';';
    (
      write_form
    ) ob x.l_stmt;
)
let write_lemma ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_lemma ob x
let string_of_lemma ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_lemma ob x;
  Bi_outbuf.contents ob
let get_lemma_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_l_user = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_l_full = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_l_stmt = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | 793355838 ->
              field_l_user := (
                (
                  read_name
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | 627113346 ->
              field_l_full := (
                (
                  read_name
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | 771228219 ->
              field_l_stmt := (
                (
                  read_form
                ) ib
              );
              bits0 := !bits0 lor 0x4;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x7 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "l_user"; "l_full"; "l_stmt" |];
        (
          {
            l_user = !field_l_user;
            l_full = !field_l_full;
            l_stmt = !field_l_stmt;
          }
         : lemma)
)
let read_lemma = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_l_user = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_l_full = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_l_stmt = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | 793355838 ->
          field_l_user := (
            (
              read_name
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | 627113346 ->
          field_l_full := (
            (
              read_name
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | 771228219 ->
          field_l_stmt := (
            (
              read_form
            ) ib
          );
          bits0 := !bits0 lor 0x4;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x7 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "l_user"; "l_full"; "l_stmt" |];
    (
      {
        l_user = !field_l_user;
        l_full = !field_l_full;
        l_stmt = !field_l_stmt;
      }
     : lemma)
)
let lemma_of_string ?pos s =
  read_lemma (Bi_inbuf.from_string ?pos s)
let env_tag = Fo_b.env_tag
let write_untagged_env = (
  Fo_b.write_untagged_env
)
let write_env ob x =
  Bi_io.write_tag ob Fo_b.env_tag;
  write_untagged_env ob x
let string_of_env ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_env ob x;
  Bi_outbuf.contents ob
let get_env_reader = (
  Fo_b.get_env_reader
)
let read_env = (
  Fo_b.read_env
)
let env_of_string ?pos s =
  read_env (Bi_inbuf.from_string ?pos s)
let _lemma_list_tag = Bi_io.array_tag
let write_untagged__lemma_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    lemma_tag
    (
      write_untagged_lemma
    )
)
let write__lemma_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__lemma_list ob x
let string_of__lemma_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__lemma_list ob x;
  Bi_outbuf.contents ob
let get__lemma_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_lemma_reader
  )
)
let read__lemma_list = (
  Atdgen_runtime.Ob_run.read_list (
    get_lemma_reader
  )
)
let _lemma_list_of_string ?pos s =
  read__lemma_list (Bi_inbuf.from_string ?pos s)
let lemmadb_tag = Bi_io.tuple_tag
let write_untagged_lemmadb = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        write_env
      ) ob x
    );
    (
      let _, x = x in (
        write__lemma_list
      ) ob x
    );
)
let write_lemmadb ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_lemmadb ob x
let string_of_lemmadb ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_lemmadb ob x;
  Bi_outbuf.contents ob
let get_lemmadb_reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            read_env
          ) ib
        in
        let x1 =
          (
            read__lemma_list
          ) ib
        in
        for i = 2 to len - 1 do Bi_io.skip ib done;
        (x0, x1)
)
let read_lemmadb = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        read_env
      ) ib
    in
    let x1 =
      (
        read__lemma_list
      ) ib
    in
    for i = 2 to len - 1 do Bi_io.skip ib done;
    (x0, x1)
)
let lemmadb_of_string ?pos s =
  read_lemmadb (Bi_inbuf.from_string ?pos s)
let expr_tag = Fo_b.expr_tag
let write_untagged_expr = (
  Fo_b.write_untagged_expr
)
let write_expr ob x =
  Bi_io.write_tag ob Fo_b.expr_tag;
  write_untagged_expr ob x
let string_of_expr ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_expr ob x;
  Bi_outbuf.contents ob
let get_expr_reader = (
  Fo_b.get_expr_reader
)
let read_expr = (
  Fo_b.read_expr
)
let expr_of_string ?pos s =
  read_expr (Bi_inbuf.from_string ?pos s)
let _lenv_lenv_expr_option_tag = Bi_io.num_variant_tag
let write_untagged__lenv_lenv_expr_option = (
  Atdgen_runtime.Ob_run.write_untagged_option (
    fun ob x ->
      Bi_io.write_tag ob Bi_io.tuple_tag;
      Bi_vint.write_uvint ob 3;
      (
        let x, _, _ = x in (
          write_lenv
        ) ob x
      );
      (
        let _, x, _ = x in (
          write_lenv
        ) ob x
      );
      (
        let _, _, x = x in (
          write_expr
        ) ob x
      );
  )
)
let write__lenv_lenv_expr_option ob x =
  Bi_io.write_tag ob Bi_io.num_variant_tag;
  write_untagged__lenv_lenv_expr_option ob x
let string_of__lenv_lenv_expr_option ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__lenv_lenv_expr_option ob x;
  Bi_outbuf.contents ob
let get__lenv_lenv_expr_option_reader = (
  fun tag ->
    if tag <> 22 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        match Char.code (Bi_inbuf.read_char ib) with
          | 0 -> None
          | 0x80 ->
            Some (
              (
                fun ib ->
                  if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                  let len = Bi_vint.read_uvint ib in
                  if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
                  let x0 =
                    (
                      read_lenv
                    ) ib
                  in
                  let x1 =
                    (
                      read_lenv
                    ) ib
                  in
                  let x2 =
                    (
                      read_expr
                    ) ib
                  in
                  for i = 3 to len - 1 do Bi_io.skip ib done;
                  (x0, x1, x2)
              )
                ib
            )
          | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let read__lenv_lenv_expr_option = (
  fun ib ->
    if Bi_io.read_tag ib <> 22 then Atdgen_runtime.Ob_run.read_error_at ib;
    match Char.code (Bi_inbuf.read_char ib) with
      | 0 -> None
      | 0x80 ->
        Some (
          (
            fun ib ->
              if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
              let len = Bi_vint.read_uvint ib in
              if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
              let x0 =
                (
                  read_lenv
                ) ib
              in
              let x1 =
                (
                  read_lenv
                ) ib
              in
              let x2 =
                (
                  read_expr
                ) ib
              in
              for i = 3 to len - 1 do Bi_io.skip ib done;
              (x0, x1, x2)
          )
            ib
        )
      | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let _lenv_lenv_expr_option_of_string ?pos s =
  read__lenv_lenv_expr_option (Bi_inbuf.from_string ?pos s)
let choice_tag = Bi_io.tuple_tag
let write_untagged_choice = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        Bi_io.write_svint
      ) ob x
    );
    (
      let _, x = x in (
        write__lenv_lenv_expr_option
      ) ob x
    );
)
let write_choice ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_choice ob x
let string_of_choice ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_choice ob x;
  Bi_outbuf.contents ob
let get_choice_reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            Atdgen_runtime.Ob_run.read_int
          ) ib
        in
        let x1 =
          (
            read__lenv_lenv_expr_option
          ) ib
        in
        for i = 2 to len - 1 do Bi_io.skip ib done;
        (x0, x1)
)
let read_choice = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        Atdgen_runtime.Ob_run.read_int
      ) ib
    in
    let x1 =
      (
        read__lenv_lenv_expr_option
      ) ib
    in
    for i = 2 to len - 1 do Bi_io.skip ib done;
    (x0, x1)
)
let choice_of_string ?pos s =
  read_choice (Bi_inbuf.from_string ?pos s)
let _choice_list_tag = Bi_io.array_tag
let write_untagged__choice_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    choice_tag
    (
      write_untagged_choice
    )
)
let write__choice_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__choice_list ob x
let string_of__choice_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__choice_list ob x;
  Bi_outbuf.contents ob
let get__choice_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_choice_reader
  )
)
let read__choice_list = (
  Atdgen_runtime.Ob_run.read_list (
    get_choice_reader
  )
)
let _choice_list_of_string ?pos s =
  read__choice_list (Bi_inbuf.from_string ?pos s)
let itrace_tag = Bi_io.array_tag
let write_untagged_itrace = (
  write_untagged__choice_list
)
let write_itrace ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged_itrace ob x
let string_of_itrace ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_itrace ob x;
  Bi_outbuf.contents ob
let get_itrace_reader = (
  get__choice_list_reader
)
let read_itrace = (
  read__choice_list
)
let itrace_of_string ?pos s =
  read_itrace (Bi_inbuf.from_string ?pos s)
let ctxt_tag = Bi_io.record_tag
let write_untagged_ctxt : Bi_outbuf.t -> ctxt -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    Bi_outbuf.add_char4 ob '\199' '\t' '\225' 'T';
    (
      write_pkind
    ) ob x.kind;
    Bi_outbuf.add_char4 ob '\183' '\253' '\131' '\168';
    (
      write_uid
    ) ob x.handle;
)
let write_ctxt ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_ctxt ob x
let string_of_ctxt ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_ctxt ob x;
  Bi_outbuf.contents ob
let get_ctxt_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_kind = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_handle = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | -955653804 ->
              field_kind := (
                (
                  read_pkind
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | 939361192 ->
              field_handle := (
                (
                  read_uid
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x3 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "kind"; "handle" |];
        (
          {
            kind = !field_kind;
            handle = !field_handle;
          }
         : ctxt)
)
let read_ctxt = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_kind = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_handle = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | -955653804 ->
          field_kind := (
            (
              read_pkind
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | 939361192 ->
          field_handle := (
            (
              read_uid
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x3 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "kind"; "handle" |];
    (
      {
        kind = !field_kind;
        handle = !field_handle;
      }
     : ctxt)
)
let ctxt_of_string ?pos s =
  read_ctxt (Bi_inbuf.from_string ?pos s)
let _int_list_tag = Bi_io.array_tag
let write_untagged__int_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.svint_tag
    (
      Bi_io.write_untagged_svint
    )
)
let write__int_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__int_list ob x
let string_of__int_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__int_list ob x;
  Bi_outbuf.contents ob
let get__int_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    Atdgen_runtime.Ob_run.get_int_reader
  )
)
let read__int_list = (
  Atdgen_runtime.Ob_run.read_list (
    Atdgen_runtime.Ob_run.get_int_reader
  )
)
let _int_list_of_string ?pos s =
  read__int_list (Bi_inbuf.from_string ?pos s)
let ipath_tag = Bi_io.record_tag
let write_untagged_ipath : Bi_outbuf.t -> ipath -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    Bi_outbuf.add_char4 ob '\193' '\200' '\141' '\237';
    (
      write_ctxt
    ) ob x.ctxt;
    Bi_outbuf.add_char4 ob '\128' 'W' '\169' '\128';
    (
      write__int_list
    ) ob x.sub;
)
let write_ipath ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_ipath ob x
let string_of_ipath ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_ipath ob x;
  Bi_outbuf.contents ob
let get_ipath_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_ctxt = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_sub = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | -1043821075 ->
              field_ctxt := (
                (
                  read_ctxt
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | 5745024 ->
              field_sub := (
                (
                  read__int_list
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x3 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "ctxt"; "sub" |];
        (
          {
            ctxt = !field_ctxt;
            sub = !field_sub;
          }
         : ipath)
)
let read_ipath = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_ctxt = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_sub = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | -1043821075 ->
          field_ctxt := (
            (
              read_ctxt
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | 5745024 ->
          field_sub := (
            (
              read__int_list
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x3 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "ctxt"; "sub" |];
    (
      {
        ctxt = !field_ctxt;
        sub = !field_sub;
      }
     : ipath)
)
let ipath_of_string ?pos s =
  read_ipath (Bi_inbuf.from_string ?pos s)
let goal_tag = Bi_io.record_tag
let write_untagged_goal : Bi_outbuf.t -> goal -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 3;
    Bi_outbuf.add_char4 ob '\141' '^' '\b' '\213';
    (
      write_env
    ) ob x.g_env;
    Bi_outbuf.add_char4 ob '\166' '\237' '\169' 'l';
    (
      write__hyp_list
    ) ob x.g_hyps;
    Bi_outbuf.add_char4 ob '\129' 'g' '\250' 'S';
    (
      write_form
    ) ob x.g_concl;
)
let write_goal ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_goal ob x
let string_of_goal ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_goal ob x;
  Bi_outbuf.contents ob
let get_goal_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_g_env = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_g_hyps = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_g_concl = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | 224266453 ->
              field_g_env := (
                (
                  read_env
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | 653109612 ->
              field_g_hyps := (
                (
                  read__hyp_list
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | 23591507 ->
              field_g_concl := (
                (
                  read_form
                ) ib
              );
              bits0 := !bits0 lor 0x4;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x7 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "g_env"; "g_hyps"; "g_concl" |];
        (
          {
            g_env = !field_g_env;
            g_hyps = !field_g_hyps;
            g_concl = !field_g_concl;
          }
         : goal)
)
let read_goal = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_g_env = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_g_hyps = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_g_concl = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | 224266453 ->
          field_g_env := (
            (
              read_env
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | 653109612 ->
          field_g_hyps := (
            (
              read__hyp_list
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | 23591507 ->
          field_g_concl := (
            (
              read_form
            ) ib
          );
          bits0 := !bits0 lor 0x4;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x7 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "g_env"; "g_hyps"; "g_concl" |];
    (
      {
        g_env = !field_g_env;
        g_hyps = !field_g_hyps;
        g_concl = !field_g_concl;
      }
     : goal)
)
let goal_of_string ?pos s =
  read_goal (Bi_inbuf.from_string ?pos s)
let _goal_list_tag = Bi_io.array_tag
let write_untagged__goal_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    goal_tag
    (
      write_untagged_goal
    )
)
let write__goal_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__goal_list ob x
let string_of__goal_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__goal_list ob x;
  Bi_outbuf.contents ob
let get__goal_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_goal_reader
  )
)
let read__goal_list = (
  Atdgen_runtime.Ob_run.read_list (
    get_goal_reader
  )
)
let _goal_list_of_string ?pos s =
  read__goal_list (Bi_inbuf.from_string ?pos s)
let goals_tag = Bi_io.array_tag
let write_untagged_goals = (
  write_untagged__goal_list
)
let write_goals ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged_goals ob x
let string_of_goals ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_goals ob x;
  Bi_outbuf.contents ob
let get_goals_reader = (
  get__goal_list_reader
)
let read_goals = (
  read__goal_list
)
let goals_of_string ?pos s =
  read_goals (Bi_inbuf.from_string ?pos s)
let bvar_tag = Fo_b.bvar_tag
let write_untagged_bvar = (
  Fo_b.write_untagged_bvar
)
let write_bvar ob x =
  Bi_io.write_tag ob Fo_b.bvar_tag;
  write_untagged_bvar ob x
let string_of_bvar ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_bvar ob x;
  Bi_outbuf.contents ob
let get_bvar_reader = (
  Fo_b.get_bvar_reader
)
let read_bvar = (
  Fo_b.read_bvar
)
let bvar_of_string ?pos s =
  read_bvar (Bi_inbuf.from_string ?pos s)
let bkind_tag = Fo_b.bkind_tag
let write_untagged_bkind = (
  Fo_b.write_untagged_bkind
)
let write_bkind ob x =
  Bi_io.write_tag ob Fo_b.bkind_tag;
  write_untagged_bkind ob x
let string_of_bkind ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_bkind ob x;
  Bi_outbuf.contents ob
let get_bkind_reader = (
  Fo_b.get_bkind_reader
)
let read_bkind = (
  Fo_b.read_bkind
)
let bkind_of_string ?pos s =
  read_bkind (Bi_inbuf.from_string ?pos s)
let arity_tag = Fo_b.arity_tag
let write_untagged_arity = (
  Fo_b.write_untagged_arity
)
let write_arity ob x =
  Bi_io.write_tag ob Fo_b.arity_tag;
  write_untagged_arity ob x
let string_of_arity ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_arity ob x;
  Bi_outbuf.contents ob
let get_arity_reader = (
  Fo_b.get_arity_reader
)
let read_arity = (
  Fo_b.read_arity
)
let arity_of_string ?pos s =
  read_arity (Bi_inbuf.from_string ?pos s)
let aident_tag = Bi_io.tuple_tag
let write_untagged_aident = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        Bi_io.write_string
      ) ob x
    );
    (
      let _, x = x in (
        write_lgoal
      ) ob x
    );
)
let write_aident ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_aident ob x
let string_of_aident ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_aident ob x;
  Bi_outbuf.contents ob
let get_aident_reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            Atdgen_runtime.Ob_run.read_string
          ) ib
        in
        let x1 =
          (
            read_lgoal
          ) ib
        in
        for i = 2 to len - 1 do Bi_io.skip ib done;
        (x0, x1)
)
let read_aident = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        Atdgen_runtime.Ob_run.read_string
      ) ib
    in
    let x1 =
      (
        read_lgoal
      ) ib
    in
    for i = 2 to len - 1 do Bi_io.skip ib done;
    (x0, x1)
)
let aident_of_string ?pos s =
  read_aident (Bi_inbuf.from_string ?pos s)
let agoal_tag = Bi_io.record_tag
let write_untagged_agoal : Bi_outbuf.t -> agoal -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 3;
    Bi_outbuf.add_char4 ob '\201' '\248' 'G' '\138';
    (
      write_varenv
    ) ob x.a_vars;
    Bi_outbuf.add_char4 ob '\192' '\201' '\127' '2';
    (
      write__hyp_list
    ) ob x.a_hyps;
    Bi_outbuf.add_char4 ob '\135' '\231' '1' '\205';
    (
      write_form
    ) ob x.a_concl;
)
let write_agoal ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_agoal ob x
let string_of_agoal ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_agoal ob x;
  Bi_outbuf.contents ob
let get_agoal_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_a_vars = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_a_hyps = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_a_concl = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | -906475638 ->
              field_a_vars := (
                (
                  read_varenv
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | -1060536526 ->
              field_a_hyps := (
                (
                  read__hyp_list
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | 132592077 ->
              field_a_concl := (
                (
                  read_form
                ) ib
              );
              bits0 := !bits0 lor 0x4;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x7 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "a_vars"; "a_hyps"; "a_concl" |];
        (
          {
            a_vars = !field_a_vars;
            a_hyps = !field_a_hyps;
            a_concl = !field_a_concl;
          }
         : agoal)
)
let read_agoal = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_a_vars = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_a_hyps = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_a_concl = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | -906475638 ->
          field_a_vars := (
            (
              read_varenv
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | -1060536526 ->
          field_a_hyps := (
            (
              read__hyp_list
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | 132592077 ->
          field_a_concl := (
            (
              read_form
            ) ib
          );
          bits0 := !bits0 lor 0x4;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x7 then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "a_vars"; "a_hyps"; "a_concl" |];
    (
      {
        a_vars = !field_a_vars;
        a_hyps = !field_a_hyps;
        a_concl = !field_a_concl;
      }
     : agoal)
)
let agoal_of_string ?pos s =
  read_agoal (Bi_inbuf.from_string ?pos s)
let _uid_option_tag = Bi_io.num_variant_tag
let write_untagged__uid_option = (
  Atdgen_runtime.Ob_run.write_untagged_option (
    write_uid
  )
)
let write__uid_option ob x =
  Bi_io.write_tag ob Bi_io.num_variant_tag;
  write_untagged__uid_option ob x
let string_of__uid_option ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__uid_option ob x;
  Bi_outbuf.contents ob
let get__uid_option_reader = (
  fun tag ->
    if tag <> 22 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        match Char.code (Bi_inbuf.read_char ib) with
          | 0 -> None
          | 0x80 ->
            Some (
              (
                read_uid
              )
                ib
            )
          | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let read__uid_option = (
  fun ib ->
    if Bi_io.read_tag ib <> 22 then Atdgen_runtime.Ob_run.read_error_at ib;
    match Char.code (Bi_inbuf.read_char ib) with
      | 0 -> None
      | 0x80 ->
        Some (
          (
            read_uid
          )
            ib
        )
      | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let _uid_option_of_string ?pos s =
  read__uid_option (Bi_inbuf.from_string ?pos s)
let _expr_type_option_tag = Bi_io.num_variant_tag
let write_untagged__expr_type_option = (
  Atdgen_runtime.Ob_run.write_untagged_option (
    fun ob x ->
      Bi_io.write_tag ob Bi_io.tuple_tag;
      Bi_vint.write_uvint ob 2;
      (
        let x, _ = x in (
          write_expr
        ) ob x
      );
      (
        let _, x = x in (
          write_type_
        ) ob x
      );
  )
)
let write__expr_type_option ob x =
  Bi_io.write_tag ob Bi_io.num_variant_tag;
  write_untagged__expr_type_option ob x
let string_of__expr_type_option ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__expr_type_option ob x;
  Bi_outbuf.contents ob
let get__expr_type_option_reader = (
  fun tag ->
    if tag <> 22 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        match Char.code (Bi_inbuf.read_char ib) with
          | 0 -> None
          | 0x80 ->
            Some (
              (
                fun ib ->
                  if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                  let len = Bi_vint.read_uvint ib in
                  if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                  let x0 =
                    (
                      read_expr
                    ) ib
                  in
                  let x1 =
                    (
                      read_type_
                    ) ib
                  in
                  for i = 2 to len - 1 do Bi_io.skip ib done;
                  (x0, x1)
              )
                ib
            )
          | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let read__expr_type_option = (
  fun ib ->
    if Bi_io.read_tag ib <> 22 then Atdgen_runtime.Ob_run.read_error_at ib;
    match Char.code (Bi_inbuf.read_char ib) with
      | 0 -> None
      | 0x80 ->
        Some (
          (
            fun ib ->
              if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
              let len = Bi_vint.read_uvint ib in
              if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
              let x0 =
                (
                  read_expr
                ) ib
              in
              let x1 =
                (
                  read_type_
                ) ib
              in
              for i = 2 to len - 1 do Bi_io.skip ib done;
              (x0, x1)
          )
            ib
        )
      | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let _expr_type_option_of_string ?pos s =
  read__expr_type_option (Bi_inbuf.from_string ?pos s)
let action_tag = Bi_io.variant_tag
let write_untagged_action = (
  fun ob x ->
    match x with
      | `AId -> Bi_outbuf.add_char4 ob '\000' '1' '\146' '|'
      | `ADef x ->
        Bi_outbuf.add_char4 ob '\171' '*' '\208' '\004';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 3;
            (
              let x, _, _ = x in (
                write_name
              ) ob x
            );
            (
              let _, x, _ = x in (
                write_type_
              ) ob x
            );
            (
              let _, _, x = x in (
                write_expr
              ) ob x
            );
        ) ob x
      | `ALemma x ->
        Bi_outbuf.add_char4 ob '\130' '\188' ',' '\'';
        (
          write_name
        ) ob x
      | `AIntro x ->
        Bi_outbuf.add_char4 ob '\206' '\128' '\174' 'k';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                Bi_io.write_svint
              ) ob x
            );
            (
              let _, x = x in (
                write__expr_type_option
              ) ob x
            );
        ) ob x
      | `AExact x ->
        Bi_outbuf.add_char4 ob '\135' 't' '\006' '\190';
        (
          write_uid
        ) ob x
      | `AElim x ->
        Bi_outbuf.add_char4 ob '\154' '\249' '\188' '\236';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_uid
              ) ob x
            );
            (
              let _, x = x in (
                Bi_io.write_svint
              ) ob x
            );
        ) ob x
      | `AInd x ->
        Bi_outbuf.add_char4 ob '\171' '.' '\163' '\030';
        (
          write_uid
        ) ob x
      | `ASimpl x ->
        Bi_outbuf.add_char4 ob '\141' '/' '\024' '\210';
        (
          write_ipath
        ) ob x
      | `ARed x ->
        Bi_outbuf.add_char4 ob '\171' '5' 'o' '\144';
        (
          write_ipath
        ) ob x
      | `AIndt x ->
        Bi_outbuf.add_char4 ob '\157' '\160' '\023' '\150';
        (
          write_ipath
        ) ob x
      | `APbp x ->
        Bi_outbuf.add_char4 ob '\171' '3' '\232' '}';
        (
          write_ipath
        ) ob x
      | `ACase x ->
        Bi_outbuf.add_char4 ob '\153' '\158' '\255' '\145';
        (
          write_ipath
        ) ob x
      | `ACut x ->
        Bi_outbuf.add_char4 ob '\171' '*' '\027' '\193';
        (
          write_form
        ) ob x
      | `AGeneralize x ->
        Bi_outbuf.add_char4 ob '\248' 'D' 'T' '\205';
        (
          write_uid
        ) ob x
      | `AMove x ->
        Bi_outbuf.add_char4 ob '\160' 'E' '\195' '\242';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_uid
              ) ob x
            );
            (
              let _, x = x in (
                write__uid_option
              ) ob x
            );
        ) ob x
      | `ADuplicate x ->
        Bi_outbuf.add_char4 ob '\149' '\210' 'q' '\n';
        (
          write_uid
        ) ob x
      | `ALink x ->
        Bi_outbuf.add_char4 ob '\159' '\151' '\248' '\219';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 3;
            (
              let x, _, _ = x in (
                write_ipath
              ) ob x
            );
            (
              let _, x, _ = x in (
                write_ipath
              ) ob x
            );
            (
              let _, _, x = x in (
                write_itrace
              ) ob x
            );
        ) ob x
      | `AInstantiate x ->
        Bi_outbuf.add_char4 ob '\139' 'e' '/' '\233';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_expr
              ) ob x
            );
            (
              let _, x = x in (
                write_ipath
              ) ob x
            );
        ) ob x
)
let write_action ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_action ob x
let string_of_action ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_action ob x;
  Bi_outbuf.contents ob
let get_action_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 3248764, false -> `AId
            | 724226052, true -> (`ADef (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
                    let x0 =
                      (
                        read_name
                      ) ib
                    in
                    let x1 =
                      (
                        read_type_
                      ) ib
                    in
                    let x2 =
                      (
                        read_expr
                      ) ib
                    in
                    for i = 3 to len - 1 do Bi_io.skip ib done;
                    (x0, x1, x2)
                ) ib
              ))
            | 45886503, true -> (`ALemma (
                (
                  read_name
                ) ib
              ))
            | -830427541, true -> (`AIntro (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        Atdgen_runtime.Ob_run.read_int
                      ) ib
                    in
                    let x1 =
                      (
                        read__expr_type_option
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | 125044414, true -> (`AExact (
                (
                  read_uid
                ) ib
              ))
            | 452574444, true -> (`AElim (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_uid
                      ) ib
                    in
                    let x1 =
                      (
                        Atdgen_runtime.Ob_run.read_int
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | 724476702, true -> (`AInd (
                (
                  read_uid
                ) ib
              ))
            | 221190354, true -> (`ASimpl (
                (
                  read_ipath
                ) ib
              ))
            | 724922256, true -> (`ARed (
                (
                  read_ipath
                ) ib
              ))
            | 497031062, true -> (`AIndt (
                (
                  read_ipath
                ) ib
              ))
            | 724822141, true -> (`APbp (
                (
                  read_ipath
                ) ib
              ))
            | 429850513, true -> (`ACase (
                (
                  read_ipath
                ) ib
              ))
            | 724179905, true -> (`ACut (
                (
                  read_form
                ) ib
              ))
            | -129739571, true -> (`AGeneralize (
                (
                  read_uid
                ) ib
              ))
            | 541443058, true -> (`AMove (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_uid
                      ) ib
                    in
                    let x1 =
                      (
                        read__uid_option
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | 366113034, true -> (`ADuplicate (
                (
                  read_uid
                ) ib
              ))
            | 530053339, true -> (`ALink (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
                    let x0 =
                      (
                        read_ipath
                      ) ib
                    in
                    let x1 =
                      (
                        read_ipath
                      ) ib
                    in
                    let x2 =
                      (
                        read_itrace
                      ) ib
                    in
                    for i = 3 to len - 1 do Bi_io.skip ib done;
                    (x0, x1, x2)
                ) ib
              ))
            | 191180777, true -> (`AInstantiate (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_expr
                      ) ib
                    in
                    let x1 =
                      (
                        read_ipath
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_action = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 3248764, false -> `AId
        | 724226052, true -> (`ADef (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
                let x0 =
                  (
                    read_name
                  ) ib
                in
                let x1 =
                  (
                    read_type_
                  ) ib
                in
                let x2 =
                  (
                    read_expr
                  ) ib
                in
                for i = 3 to len - 1 do Bi_io.skip ib done;
                (x0, x1, x2)
            ) ib
          ))
        | 45886503, true -> (`ALemma (
            (
              read_name
            ) ib
          ))
        | -830427541, true -> (`AIntro (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    Atdgen_runtime.Ob_run.read_int
                  ) ib
                in
                let x1 =
                  (
                    read__expr_type_option
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | 125044414, true -> (`AExact (
            (
              read_uid
            ) ib
          ))
        | 452574444, true -> (`AElim (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_uid
                  ) ib
                in
                let x1 =
                  (
                    Atdgen_runtime.Ob_run.read_int
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | 724476702, true -> (`AInd (
            (
              read_uid
            ) ib
          ))
        | 221190354, true -> (`ASimpl (
            (
              read_ipath
            ) ib
          ))
        | 724922256, true -> (`ARed (
            (
              read_ipath
            ) ib
          ))
        | 497031062, true -> (`AIndt (
            (
              read_ipath
            ) ib
          ))
        | 724822141, true -> (`APbp (
            (
              read_ipath
            ) ib
          ))
        | 429850513, true -> (`ACase (
            (
              read_ipath
            ) ib
          ))
        | 724179905, true -> (`ACut (
            (
              read_form
            ) ib
          ))
        | -129739571, true -> (`AGeneralize (
            (
              read_uid
            ) ib
          ))
        | 541443058, true -> (`AMove (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_uid
                  ) ib
                in
                let x1 =
                  (
                    read__uid_option
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | 366113034, true -> (`ADuplicate (
            (
              read_uid
            ) ib
          ))
        | 530053339, true -> (`ALink (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 3 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2 ];
                let x0 =
                  (
                    read_ipath
                  ) ib
                in
                let x1 =
                  (
                    read_ipath
                  ) ib
                in
                let x2 =
                  (
                    read_itrace
                  ) ib
                in
                for i = 3 to len - 1 do Bi_io.skip ib done;
                (x0, x1, x2)
            ) ib
          ))
        | 191180777, true -> (`AInstantiate (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_expr
                  ) ib
                in
                let x1 =
                  (
                    read_ipath
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let action_of_string ?pos s =
  read_action (Bi_inbuf.from_string ?pos s)
