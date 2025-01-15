module File = struct
  let read_file_from_channel ic =
    let crlf = Str.regexp "\r\n" in
    let lines = ref [] in
    (try
       while true do
         lines := input_line ic :: !lines
       done
     with
     | End_of_file -> ());
    !lines |> List.rev |> String.concat "\n" |> Str.global_substitute crlf (fun _ -> "\n")
  ;;

  let read_file_from_path path =
    let ic = open_in path in
    let res = read_file_from_channel ic in
    close_in ic;
    res
  ;;

  let write_file_to_channel oc string =
    let string =
      if Core.String.is_suffix string ~suffix:"\n" then string else string ^ "\n"
    in
    output_string oc string
  ;;

  let write_file_to_path path string = write_file_to_channel (open_out path) string
end
