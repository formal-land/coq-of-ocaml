require 'erb'
include(ERB::Util)

coq_kernel_directory = ARGV[0]

conversions = []
Dir.glob(File.join(coq_kernel_directory, "*.ml")).each do |ocaml_file_name|
  ocaml_name = File.basename(ocaml_file_name)
  ocaml_content = File.read(ocaml_file_name)
  coq_file_name = File.join(
    File.dirname(ocaml_file_name),
    File.basename(ocaml_file_name, ".ml") + ".v"
  )
  coq_name = File.basename(coq_file_name)
  if File.exists?(coq_file_name) then
    coq_content = File.read(coq_file_name)
    conversions << [ocaml_name, ocaml_content, coq_name, coq_content]
  end
end
conversions.sort_by! {|ocaml_name, _, _, _| ocaml_name}

renderer = ERB.new(File.read("index.html.erb"))
File.open("index.html", "w") do |file|
  file << renderer.result()
end
