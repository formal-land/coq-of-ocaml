let () =
  let _ = 1 + 1 in
  ignore 2;
  ()

module M = struct
  ignore (1 + 1)
end
