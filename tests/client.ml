open Unix
open Api.Logic_b
open Api.Logic_t

let () =
  let addr = ADDR_INET (inet_addr_of_string "127.0.0.1", 8124) in
  let (cin, cout) = open_connection addr in
  Printf.fprintf cout "coucou\n";
  Printf.fprintf cout "ça va ?\n";
  flush cout;
  shutdown_connection cin