# encoding: UTF-8
require 'erb'
require 'json'
require 'pathname'
include(ERB::Util)

def mark_text(text, errors)
  bytes_errors = text.bytes.to_a.map {|byte| {byte: byte, errors: []}}
  errors.each do |error|
    error["location"]["start"].upto(error["location"]["end"] - 1) do |byte_index|
      if bytes_errors[byte_index] then
        bytes_errors[byte_index][:errors] << error
      end
    end
  end

  fragments = [{errors: [], text_bytes: []}]
  bytes_errors.each do |current_errors|
    if current_errors[:errors] == fragments[-1][:errors] then
      fragments[-1][:text_bytes] << current_errors[:byte]
    else
      fragments << {errors: current_errors[:errors].dup, text_bytes: [current_errors[:byte]]}
    end
  end

  output = ""
  fragments.each do |fragment|
    encoded_text = h(fragment[:text_bytes].pack("U*"))
    encoded_errors = h(fragment[:errors].map {|error| error["message"]}.join("\n\n" + "—" * 10 + "\n\n"))
    if fragment[:errors].size == 0 then
      output << encoded_text
    else
      output << "<abbr class=\"mark\" title=\"#{encoded_errors}\">#{encoded_text}</abbr>"
    end
  end
  output
end

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
  errors_file_name = ocaml_file_name + ".errors"
  coq_name = File.basename(coq_file_name)
  if File.exists?(coq_file_name) then
    coq_content = File.read(coq_file_name)
    errors_content = File.read(errors_file_name)
    errors_json = errors_content != "" ? JSON.parse(errors_content) : []
    kernel_conversions << [
      ocaml_name,
      errors_json.size,
      mark_text(ocaml_content, errors_json),
      coq_name,
      coq_content
    ]
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
