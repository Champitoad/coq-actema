open Api

type proof = (int * Logic.action) list

let hash_of (s : string) : string =
  s |> Sha512.string |> Sha512.to_bin |> Base64.encode_string ~alphabet:Base64.uri_safe_alphabet

let hash_of_aident (id : Logic.aident) : string = id |> Logic.show_aident |> hash_of

let proofs_folder () : string =
  let root_path = Loadpath.find_load_path "." |> Loadpath.physical in
  root_path ^ "/actema.proofs"

let path_of_proof (id : Logic.aident) : string =
  Format.sprintf "%s/%s" (proofs_folder ()) (hash_of_aident id)

(* I was a bit lazy here in using Marshal to save proofs.
   A better solution would probably be to use a text format such as
   JSON or Biniou. *)
let save_proof (id : Logic.aident) (prf : proof) : unit =
  let path = path_of_proof id in

  if not (CUnix.file_readable_p (proofs_folder ()))
  then begin
    let status = CUnix.sys_command "mkdir" [ proofs_folder () ] in
    match status with
    | WEXITED 0 -> ()
    | _ ->
        let err_msg = Printf.sprintf "Could not create directory %s" (proofs_folder ()) in
        raise (Sys_error err_msg)
  end;
  let oc = open_out path in
  prf
  |> List.iter
       begin
         fun (idx, action) ->
           let actionb = action |> Fun.flip Marshal.to_string [] |> Base64.encode_exn in
           Printf.fprintf oc "%d\n%s\n" idx actionb
       end;
  close_out oc

let load_proof (id : Logic.aident) : proof option =
  let path = path_of_proof id in
  if not (CUnix.file_readable_p path)
  then None
  else begin
    let ic = open_in path in
    let prf : proof ref = ref [] in
    begin
      try
        while true do
          let line = input_line ic in
          let idx = line |> int_of_string in

          let line = input_line ic in
          let action : Logic.action = line |> Base64.decode_exn |> Fun.flip Marshal.from_string 0 in

          prf := (idx, action) :: !prf
        done
      with End_of_file -> close_in ic
    end;
    let prf = List.rev !prf in
    Some prf
  end
