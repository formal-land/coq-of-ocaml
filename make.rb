# encoding: UTF-8
require 'erb'
require 'pathname'
include(ERB::Util)

kernel_directory, tezos_directory = ARGV

# Get the conversions for the Coq kernel.
kernel_conversions = []
Dir.glob(File.join(kernel_directory, "*.ml")).each do |ocaml_file_name|
  ocaml_name = File.basename(ocaml_file_name)
  ocaml_content = File.read(ocaml_file_name)
  coq_file_name = File.join(
    File.dirname(ocaml_file_name),
    File.basename(ocaml_file_name, ".ml") + ".v"
  )
  coq_name = File.basename(coq_file_name)
  if File.exists?(coq_file_name) then
    coq_content = File.read(coq_file_name)
    kernel_conversions << [ocaml_name, ocaml_content, coq_name, coq_content]
  end
end
kernel_conversions.sort_by! {|ocaml_name, _, _, _| ocaml_name}

# Get the conversions for Tezos.
tezos_conversions = []
Dir.glob(File.join(tezos_directory, "**", "*.ml*")).each do |ocaml_file_name|
  ocaml_name = Pathname.new(ocaml_file_name).relative_path_from(Pathname.new(tezos_directory)).to_s
  ocaml_content = File.read(ocaml_file_name, :encoding => 'utf-8')
  coq_file_name = ocaml_file_name + ".v"
  coq_name = ocaml_name + ".v"
  if File.exists?(coq_file_name) then
    coq_content = File.read(coq_file_name, :encoding => 'utf-8')
    if coq_content.valid_encoding? then
      coq_content.gsub!("❌", "🔥")
      tezos_conversions << [ocaml_name, ocaml_content, coq_name, coq_content]
    end
  end
end
tezos_conversions.sort_by! {|ocaml_name, _, _, _| ocaml_name}

# Helpers.
def header(root, section)
  ERB.new(File.read("template/header.html.erb")).result(binding)
end

def footer(root)
  ERB.new(File.read("template/footer.html.erb")).result(binding)
end

# Generate the files.
File.open("index.html", "w") do |file|
  file << ERB.new(File.read("index.html.erb")).result(binding)
end

File.open("kernel/index.html", "w") do |file|
  file << ERB.new(File.read("kernel.html.erb")).result(binding)
end

File.open("tezos/index.html", "w") do |file|
  file << ERB.new(File.read("tezos.html.erb")).result(binding)
end
