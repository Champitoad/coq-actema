(* Auto-generated from "fo.atd" *)
[@@@ocaml.warning "-27-32-33-35-39"]

type bkind = Fo_t.bkind

type logcon = Fo_t.logcon

type name = Fo_t.name

type type_ = Fo_t.type_

type expr = Fo_t.expr

type form = Fo_t.form

type bvar = Fo_t.bvar

type varenv = Fo_t.varenv

type term = Fo_t.term

type arity = Fo_t.arity

type sig_ = Fo_t.sig_

type lenv = Fo_t.lenv

type env = Fo_t.env = {
  env_sort: name list;
  env_prp: (name * arity) list;
  env_fun: (name * sig_) list;
  env_sort_name: (name * name) list;
  env_prp_name: (name * name) list;
  env_fun_name: (name * name) list;
  env_var: varenv
}

let bkind_tag = Bi_io.variant_tag
let write_untagged_bkind = (
  fun ob x ->
    match x with
      | `Forall -> Bi_outbuf.add_char4 ob '2' '\025' '\241' '\216'
      | `Exist -> Bi_outbuf.add_char4 ob '\n' 'G' '\178' '\151'
)
let write_bkind ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_bkind ob x
let string_of_bkind ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_bkind ob x;
  Bi_outbuf.contents ob
let get_bkind_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 840561112, false -> `Forall
            | 172470935, false -> `Exist
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_bkind = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 840561112, false -> `Forall
        | 172470935, false -> `Exist
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let bkind_of_string ?pos s =
  read_bkind (Bi_inbuf.from_string ?pos s)
let logcon_tag = Bi_io.variant_tag
let write_untagged_logcon = (
  fun ob x ->
    match x with
      | `And -> Bi_outbuf.add_char4 ob '\000' '1' '\178' '\183'
      | `Or -> Bi_outbuf.add_char4 ob '\000' '\000' 'E' 'C'
      | `Imp -> Bi_outbuf.add_char4 ob '\000' '7' '\195' '\236'
      | `Equiv -> Bi_outbuf.add_char4 ob '\005' '\176' 'F' '\150'
      | `Not -> Bi_outbuf.add_char4 ob '\000' ';' '\144' '\243'
)
let write_logcon ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_logcon ob x
let string_of_logcon ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_logcon ob x;
  Bi_outbuf.contents ob
let get_logcon_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 3257015, false -> `And
            | 17731, false -> `Or
            | 3654636, false -> `Imp
            | 95438486, false -> `Equiv
            | 3903731, false -> `Not
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_logcon = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 3257015, false -> `And
        | 17731, false -> `Or
        | 3654636, false -> `Imp
        | 95438486, false -> `Equiv
        | 3903731, false -> `Not
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let logcon_of_string ?pos s =
  read_logcon (Bi_inbuf.from_string ?pos s)
let name_tag = Bi_io.string_tag
let write_untagged_name = (
  Bi_io.write_untagged_string
)
let write_name ob x =
  Bi_io.write_tag ob Bi_io.string_tag;
  write_untagged_name ob x
let string_of_name ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_name ob x;
  Bi_outbuf.contents ob
let get_name_reader = (
  Atdgen_runtime.Ob_run.get_string_reader
)
let read_name = (
  Atdgen_runtime.Ob_run.read_string
)
let name_of_string ?pos s =
  read_name (Bi_inbuf.from_string ?pos s)
let type__tag = Bi_io.variant_tag
let write_untagged_type_ = (
  fun ob x ->
    match x with
      | `TVar x ->
        Bi_outbuf.add_char4 ob '\183' '\199' '\130' '\243';
        (
          write_name
        ) ob x
)
let write_type_ ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_type_ ob x
let string_of_type_ ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_type_ ob x;
  Bi_outbuf.contents ob
let get_type__reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 935822067, true -> (`TVar (
                (
                  read_name
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_type_ = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 935822067, true -> (`TVar (
            (
              read_name
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let type__of_string ?pos s =
  read_type_ (Bi_inbuf.from_string ?pos s)
let rec _expr_list_tag = Bi_io.array_tag
and write_untagged__expr_list ob x = (
  Atdgen_runtime.Ob_run.write_untagged_list
    expr_tag
    (
      write_untagged_expr
    )
) ob x
and write__expr_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__expr_list ob x
and string_of__expr_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__expr_list ob x;
  Bi_outbuf.contents ob
and expr_tag = Bi_io.variant_tag
and write_untagged_expr = (
  fun ob x ->
    match x with
      | `EVar x ->
        Bi_outbuf.add_char4 ob '\173' '\221' 'O' '\162';
        (
          write_name
        ) ob x
      | `EFun x ->
        Bi_outbuf.add_char4 ob '\173' '\209' '<' '\250';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_name
              ) ob x
            );
            (
              let _, x = x in (
                write__expr_list
              ) ob x
            );
        ) ob x
)
and write_expr ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_expr ob x
and string_of_expr ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_expr ob x;
  Bi_outbuf.contents ob
let rec get__expr_list_reader tag = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_expr_reader
  )
) tag
and read__expr_list ib = (
  Atdgen_runtime.Ob_run.read_list (
    get_expr_reader
  )
) ib
and _expr_list_of_string ?pos s =
  read__expr_list (Bi_inbuf.from_string ?pos s)
and get_expr_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 769478562, true -> (`EVar (
                (
                  read_name
                ) ib
              ))
            | 768687354, true -> (`EFun (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_name
                      ) ib
                    in
                    let x1 =
                      (
                        read__expr_list
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
and read_expr = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 769478562, true -> (`EVar (
            (
              read_name
            ) ib
          ))
        | 768687354, true -> (`EFun (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_name
                  ) ib
                in
                let x1 =
                  (
                    read__expr_list
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
and expr_of_string ?pos s =
  read_expr (Bi_inbuf.from_string ?pos s)
let rec _form_list_tag = Bi_io.array_tag
and write_untagged__form_list ob x = (
  Atdgen_runtime.Ob_run.write_untagged_list
    form_tag
    (
      write_untagged_form
    )
) ob x
and write__form_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__form_list ob x
and string_of__form_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__form_list ob x;
  Bi_outbuf.contents ob
and form_tag = Bi_io.variant_tag
and write_untagged_form = (
  fun ob x ->
    match x with
      | `FTrue -> Bi_outbuf.add_char4 ob '\005' '\233' 'n' '\180'
      | `FFalse -> Bi_outbuf.add_char4 ob '\011' 'w' '\231' '}'
      | `FPred x ->
        Bi_outbuf.add_char4 ob '\131' 'D' '\134' 'G';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_name
              ) ob x
            );
            (
              let _, x = x in (
                write__expr_list
              ) ob x
            );
        ) ob x
      | `FConn x ->
        Bi_outbuf.add_char4 ob '\250' '\170' '\129' 'R';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 2;
            (
              let x, _ = x in (
                write_logcon
              ) ob x
            );
            (
              let _, x = x in (
                write__form_list
              ) ob x
            );
        ) ob x
      | `FBind x ->
        Bi_outbuf.add_char4 ob '\249' '\252' '\189' '#';
        (
          fun ob x ->
            Bi_io.write_tag ob Bi_io.tuple_tag;
            Bi_vint.write_uvint ob 4;
            (
              let x, _, _, _ = x in (
                write_bkind
              ) ob x
            );
            (
              let _, x, _, _ = x in (
                write_name
              ) ob x
            );
            (
              let _, _, x, _ = x in (
                write_type_
              ) ob x
            );
            (
              let _, _, _, x = x in (
                write_form
              ) ob x
            );
        ) ob x
)
and write_form ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_form ob x
and string_of_form ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_form ob x;
  Bi_outbuf.contents ob
let rec get__form_list_reader tag = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_form_reader
  )
) tag
and read__form_list ib = (
  Atdgen_runtime.Ob_run.read_list (
    get_form_reader
  )
) ib
and _form_list_of_string ?pos s =
  read__form_list (Bi_inbuf.from_string ?pos s)
and get_form_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 99184308, false -> `FTrue
            | 192407421, false -> `FFalse
            | 54822471, true -> (`FPred (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_name
                      ) ib
                    in
                    let x1 =
                      (
                        read__expr_list
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | -89489070, true -> (`FConn (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                    let x0 =
                      (
                        read_logcon
                      ) ib
                    in
                    let x1 =
                      (
                        read__form_list
                      ) ib
                    in
                    for i = 2 to len - 1 do Bi_io.skip ib done;
                    (x0, x1)
                ) ib
              ))
            | -100877021, true -> (`FBind (
                (
                  fun ib ->
                    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                    let len = Bi_vint.read_uvint ib in
                    if len < 4 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2; 3 ];
                    let x0 =
                      (
                        read_bkind
                      ) ib
                    in
                    let x1 =
                      (
                        read_name
                      ) ib
                    in
                    let x2 =
                      (
                        read_type_
                      ) ib
                    in
                    let x3 =
                      (
                        read_form
                      ) ib
                    in
                    for i = 4 to len - 1 do Bi_io.skip ib done;
                    (x0, x1, x2, x3)
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
and read_form = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 99184308, false -> `FTrue
        | 192407421, false -> `FFalse
        | 54822471, true -> (`FPred (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_name
                  ) ib
                in
                let x1 =
                  (
                    read__expr_list
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | -89489070, true -> (`FConn (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
                let x0 =
                  (
                    read_logcon
                  ) ib
                in
                let x1 =
                  (
                    read__form_list
                  ) ib
                in
                for i = 2 to len - 1 do Bi_io.skip ib done;
                (x0, x1)
            ) ib
          ))
        | -100877021, true -> (`FBind (
            (
              fun ib ->
                if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
                let len = Bi_vint.read_uvint ib in
                if len < 4 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1; 2; 3 ];
                let x0 =
                  (
                    read_bkind
                  ) ib
                in
                let x1 =
                  (
                    read_name
                  ) ib
                in
                let x2 =
                  (
                    read_type_
                  ) ib
                in
                let x3 =
                  (
                    read_form
                  ) ib
                in
                for i = 4 to len - 1 do Bi_io.skip ib done;
                (x0, x1, x2, x3)
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
and form_of_string ?pos s =
  read_form (Bi_inbuf.from_string ?pos s)
let _expr_option_tag = Bi_io.num_variant_tag
let write_untagged__expr_option = (
  Atdgen_runtime.Ob_run.write_untagged_option (
    write_expr
  )
)
let write__expr_option ob x =
  Bi_io.write_tag ob Bi_io.num_variant_tag;
  write_untagged__expr_option ob x
let string_of__expr_option ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__expr_option ob x;
  Bi_outbuf.contents ob
let get__expr_option_reader = (
  fun tag ->
    if tag <> 22 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        match Char.code (Bi_inbuf.read_char ib) with
          | 0 -> None
          | 0x80 ->
            Some (
              (
                read_expr
              )
                ib
            )
          | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let read__expr_option = (
  fun ib ->
    if Bi_io.read_tag ib <> 22 then Atdgen_runtime.Ob_run.read_error_at ib;
    match Char.code (Bi_inbuf.read_char ib) with
      | 0 -> None
      | 0x80 ->
        Some (
          (
            read_expr
          )
            ib
        )
      | _ -> Atdgen_runtime.Ob_run.read_error_at ib
)
let _expr_option_of_string ?pos s =
  read__expr_option (Bi_inbuf.from_string ?pos s)
let bvar_tag = Bi_io.tuple_tag
let write_untagged_bvar = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        write_type_
      ) ob x
    );
    (
      let _, x = x in (
        write__expr_option
      ) ob x
    );
)
let write_bvar ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_bvar ob x
let string_of_bvar ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_bvar ob x;
  Bi_outbuf.contents ob
let get_bvar_reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            read_type_
          ) ib
        in
        let x1 =
          (
            read__expr_option
          ) ib
        in
        for i = 2 to len - 1 do Bi_io.skip ib done;
        (x0, x1)
)
let read_bvar = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        read_type_
      ) ib
    in
    let x1 =
      (
        read__expr_option
      ) ib
    in
    for i = 2 to len - 1 do Bi_io.skip ib done;
    (x0, x1)
)
let bvar_of_string ?pos s =
  read_bvar (Bi_inbuf.from_string ?pos s)
let _name_bvar_list_tag = Bi_io.array_tag
let write_untagged__name_bvar_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_name
          ) ob x
        );
        (
          let _, x = x in (
            write_bvar
          ) ob x
        );
    )
)
let write__name_bvar_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__name_bvar_list ob x
let string_of__name_bvar_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__name_bvar_list ob x;
  Bi_outbuf.contents ob
let get__name_bvar_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_bvar
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__name_bvar_list = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_bvar
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _name_bvar_list_of_string ?pos s =
  read__name_bvar_list (Bi_inbuf.from_string ?pos s)
let varenv_tag = Bi_io.array_tag
let write_untagged_varenv = (
  write_untagged__name_bvar_list
)
let write_varenv ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged_varenv ob x
let string_of_varenv ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_varenv ob x;
  Bi_outbuf.contents ob
let get_varenv_reader = (
  get__name_bvar_list_reader
)
let read_varenv = (
  read__name_bvar_list
)
let varenv_of_string ?pos s =
  read_varenv (Bi_inbuf.from_string ?pos s)
let term_tag = Bi_io.variant_tag
let write_untagged_term = (
  fun ob x ->
    match x with
      | `F x ->
        Bi_outbuf.add_char4 ob '\128' '\000' '\000' 'F';
        (
          write_form
        ) ob x
      | `E x ->
        Bi_outbuf.add_char4 ob '\128' '\000' '\000' 'E';
        (
          write_expr
        ) ob x
)
let write_term ob x =
  Bi_io.write_tag ob Bi_io.variant_tag;
  write_untagged_term ob x
let string_of_term ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_term ob x;
  Bi_outbuf.contents ob
let get_term_reader = (
  fun tag ->
    if tag <> 23 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        Bi_io.read_hashtag ib (fun ib h has_arg ->
          match h, has_arg with
            | 70, true -> (`F (
                (
                  read_form
                ) ib
              ))
            | 69, true -> (`E (
                (
                  read_expr
                ) ib
              ))
            | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
        )
)
let read_term = (
  fun ib ->
    if Bi_io.read_tag ib <> 23 then Atdgen_runtime.Ob_run.read_error_at ib;
    Bi_io.read_hashtag ib (fun ib h has_arg ->
      match h, has_arg with
        | 70, true -> (`F (
            (
              read_form
            ) ib
          ))
        | 69, true -> (`E (
            (
              read_expr
            ) ib
          ))
        | _ -> Atdgen_runtime.Ob_run.unsupported_variant h has_arg
    )
)
let term_of_string ?pos s =
  read_term (Bi_inbuf.from_string ?pos s)
let _type_list_tag = Bi_io.array_tag
let write_untagged__type_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    type__tag
    (
      write_untagged_type_
    )
)
let write__type_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__type_list ob x
let string_of__type_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__type_list ob x;
  Bi_outbuf.contents ob
let get__type_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_type__reader
  )
)
let read__type_list = (
  Atdgen_runtime.Ob_run.read_list (
    get_type__reader
  )
)
let _type_list_of_string ?pos s =
  read__type_list (Bi_inbuf.from_string ?pos s)
let arity_tag = Bi_io.array_tag
let write_untagged_arity = (
  write_untagged__type_list
)
let write_arity ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged_arity ob x
let string_of_arity ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_arity ob x;
  Bi_outbuf.contents ob
let get_arity_reader = (
  get__type_list_reader
)
let read_arity = (
  read__type_list
)
let arity_of_string ?pos s =
  read_arity (Bi_inbuf.from_string ?pos s)
let sig__tag = Bi_io.tuple_tag
let write_untagged_sig_ = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    (
      let x, _ = x in (
        write_arity
      ) ob x
    );
    (
      let _, x = x in (
        write_type_
      ) ob x
    );
)
let write_sig_ ob x =
  Bi_io.write_tag ob Bi_io.tuple_tag;
  write_untagged_sig_ ob x
let string_of_sig_ ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_sig_ ob x;
  Bi_outbuf.contents ob
let get_sig__reader = (
  fun tag ->
    if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let len = Bi_vint.read_uvint ib in
        if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
        let x0 =
          (
            read_arity
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
let read_sig_ = (
  fun ib ->
    if Bi_io.read_tag ib <> 20 then Atdgen_runtime.Ob_run.read_error_at ib;
    let len = Bi_vint.read_uvint ib in
    if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
    let x0 =
      (
        read_arity
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
let sig__of_string ?pos s =
  read_sig_ (Bi_inbuf.from_string ?pos s)
let _name_type_list_tag = Bi_io.array_tag
let write_untagged__name_type_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_name
          ) ob x
        );
        (
          let _, x = x in (
            write_type_
          ) ob x
        );
    )
)
let write__name_type_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__name_type_list ob x
let string_of__name_type_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__name_type_list ob x;
  Bi_outbuf.contents ob
let get__name_type_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
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
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__name_type_list = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
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
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _name_type_list_of_string ?pos s =
  read__name_type_list (Bi_inbuf.from_string ?pos s)
let lenv_tag = Bi_io.array_tag
let write_untagged_lenv = (
  write_untagged__name_type_list
)
let write_lenv ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged_lenv ob x
let string_of_lenv ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_lenv ob x;
  Bi_outbuf.contents ob
let get_lenv_reader = (
  get__name_type_list_reader
)
let read_lenv = (
  read__name_type_list
)
let lenv_of_string ?pos s =
  read_lenv (Bi_inbuf.from_string ?pos s)
let _name_sig_list_tag = Bi_io.array_tag
let write_untagged__name_sig_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_name
          ) ob x
        );
        (
          let _, x = x in (
            write_sig_
          ) ob x
        );
    )
)
let write__name_sig_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__name_sig_list ob x
let string_of__name_sig_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__name_sig_list ob x;
  Bi_outbuf.contents ob
let get__name_sig_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_sig_
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__name_sig_list = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_sig_
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _name_sig_list_of_string ?pos s =
  read__name_sig_list (Bi_inbuf.from_string ?pos s)
let _name_name_list_tag = Bi_io.array_tag
let write_untagged__name_name_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_name
          ) ob x
        );
        (
          let _, x = x in (
            write_name
          ) ob x
        );
    )
)
let write__name_name_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__name_name_list ob x
let string_of__name_name_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__name_name_list ob x;
  Bi_outbuf.contents ob
let get__name_name_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_name
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__name_name_list = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_name
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _name_name_list_of_string ?pos s =
  read__name_name_list (Bi_inbuf.from_string ?pos s)
let _name_list_tag = Bi_io.array_tag
let write_untagged__name_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    name_tag
    (
      write_untagged_name
    )
)
let write__name_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__name_list ob x
let string_of__name_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__name_list ob x;
  Bi_outbuf.contents ob
let get__name_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    get_name_reader
  )
)
let read__name_list = (
  Atdgen_runtime.Ob_run.read_list (
    get_name_reader
  )
)
let _name_list_of_string ?pos s =
  read__name_list (Bi_inbuf.from_string ?pos s)
let _name_arity_list_tag = Bi_io.array_tag
let write_untagged__name_arity_list = (
  Atdgen_runtime.Ob_run.write_untagged_list
    Bi_io.tuple_tag
    (
      fun ob x ->
        Bi_vint.write_uvint ob 2;
        (
          let x, _ = x in (
            write_name
          ) ob x
        );
        (
          let _, x = x in (
            write_arity
          ) ob x
        );
    )
)
let write__name_arity_list ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__name_arity_list ob x
let string_of__name_arity_list ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__name_arity_list ob x;
  Bi_outbuf.contents ob
let get__name_arity_list_reader = (
  Atdgen_runtime.Ob_run.get_list_reader (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_arity
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let read__name_arity_list = (
  Atdgen_runtime.Ob_run.read_list (
    fun tag ->
      if tag <> 20 then Atdgen_runtime.Ob_run.read_error () else
        fun ib ->
          let len = Bi_vint.read_uvint ib in
          if len < 2 then Atdgen_runtime.Ob_run.missing_tuple_fields len [ 0; 1 ];
          let x0 =
            (
              read_name
            ) ib
          in
          let x1 =
            (
              read_arity
            ) ib
          in
          for i = 2 to len - 1 do Bi_io.skip ib done;
          (x0, x1)
  )
)
let _name_arity_list_of_string ?pos s =
  read__name_arity_list (Bi_inbuf.from_string ?pos s)
let env_tag = Bi_io.record_tag
let write_untagged_env : Bi_outbuf.t -> env -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 7;
    Bi_outbuf.add_char4 ob '\156' '\165' '\228' '0';
    (
      write__name_list
    ) ob x.env_sort;
    Bi_outbuf.add_char4 ob '\147' '\162' '\163' '\156';
    (
      write__name_arity_list
    ) ob x.env_prp;
    Bi_outbuf.add_char4 ob '\147' '\155' '\015' '\173';
    (
      write__name_sig_list
    ) ob x.env_fun;
    Bi_outbuf.add_char4 ob '\248' '\177' '{' '\250';
    (
      write__name_name_list
    ) ob x.env_sort_name;
    Bi_outbuf.add_char4 ob '\136' '\171' 'U' '\014';
    (
      write__name_name_list
    ) ob x.env_prp_name;
    Bi_outbuf.add_char4 ob '\252' '\188' '\139' ']';
    (
      write__name_name_list
    ) ob x.env_fun_name;
    Bi_outbuf.add_char4 ob '\147' '\167' '"' 'U';
    (
      write_varenv
    ) ob x.env_var;
)
let write_env ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_env ob x
let string_of_env ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_env ob x;
  Bi_outbuf.contents ob
let get_env_reader = (
  fun tag ->
    if tag <> 21 then Atdgen_runtime.Ob_run.read_error () else
      fun ib ->
        let field_env_sort = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_prp = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_fun = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_sort_name = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_prp_name = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_fun_name = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let field_env_var = ref (Obj.magic (Sys.opaque_identity 0.0)) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | 480633904 ->
              field_env_sort := (
                (
                  read__name_list
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | 329425820 ->
              field_env_prp := (
                (
                  read__name_arity_list
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | 328929197 ->
              field_env_fun := (
                (
                  read__name_sig_list
                ) ib
              );
              bits0 := !bits0 lor 0x4;
            | -122586118 ->
              field_env_sort_name := (
                (
                  read__name_name_list
                ) ib
              );
              bits0 := !bits0 lor 0x8;
            | 145446158 ->
              field_env_prp_name := (
                (
                  read__name_name_list
                ) ib
              );
              bits0 := !bits0 lor 0x10;
            | -54752419 ->
              field_env_fun_name := (
                (
                  read__name_name_list
                ) ib
              );
              bits0 := !bits0 lor 0x20;
            | 329720405 ->
              field_env_var := (
                (
                  read_varenv
                ) ib
              );
              bits0 := !bits0 lor 0x40;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x7f then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "env_sort"; "env_prp"; "env_fun"; "env_sort_name"; "env_prp_name"; "env_fun_name"; "env_var" |];
        (
          {
            env_sort = !field_env_sort;
            env_prp = !field_env_prp;
            env_fun = !field_env_fun;
            env_sort_name = !field_env_sort_name;
            env_prp_name = !field_env_prp_name;
            env_fun_name = !field_env_fun_name;
            env_var = !field_env_var;
          }
         : env)
)
let read_env = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Atdgen_runtime.Ob_run.read_error_at ib;
    let field_env_sort = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_prp = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_fun = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_sort_name = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_prp_name = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_fun_name = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let field_env_var = ref (Obj.magic (Sys.opaque_identity 0.0)) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | 480633904 ->
          field_env_sort := (
            (
              read__name_list
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | 329425820 ->
          field_env_prp := (
            (
              read__name_arity_list
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | 328929197 ->
          field_env_fun := (
            (
              read__name_sig_list
            ) ib
          );
          bits0 := !bits0 lor 0x4;
        | -122586118 ->
          field_env_sort_name := (
            (
              read__name_name_list
            ) ib
          );
          bits0 := !bits0 lor 0x8;
        | 145446158 ->
          field_env_prp_name := (
            (
              read__name_name_list
            ) ib
          );
          bits0 := !bits0 lor 0x10;
        | -54752419 ->
          field_env_fun_name := (
            (
              read__name_name_list
            ) ib
          );
          bits0 := !bits0 lor 0x20;
        | 329720405 ->
          field_env_var := (
            (
              read_varenv
            ) ib
          );
          bits0 := !bits0 lor 0x40;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x7f then Atdgen_runtime.Ob_run.missing_fields [| !bits0 |] [| "env_sort"; "env_prp"; "env_fun"; "env_sort_name"; "env_prp_name"; "env_fun_name"; "env_var" |];
    (
      {
        env_sort = !field_env_sort;
        env_prp = !field_env_prp;
        env_fun = !field_env_fun;
        env_sort_name = !field_env_sort_name;
        env_prp_name = !field_env_prp_name;
        env_fun_name = !field_env_fun_name;
        env_var = !field_env_var;
      }
     : env)
)
let env_of_string ?pos s =
  read_env (Bi_inbuf.from_string ?pos s)
