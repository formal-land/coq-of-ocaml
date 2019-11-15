# encoding: UTF-8
require 'erb'
require 'json'
require 'pathname'
include(ERB::Util)

# Command line arguments.
kernel_directory, tezos_directory = ARGV

def mark_text(text, errors)
  bytes_errors = text.bytes.to_a.map {|byte| {byte: byte, errors: []}}
  global_errors = []
  errors.each do |error|
    if error["location"]["start"] >= 0 && error["location"]["end"] >= 0 then
      error["location"]["start"].upto(error["location"]["end"] - 1) do |byte_index|
        if bytes_errors[byte_index] then
          bytes_errors[byte_index][:errors] << error
        end
      end
    else
      global_errors << error["message"]
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
      output << "<abbr class=\"mark-error\" title=\"#{encoded_errors}\">#{encoded_text}</abbr>"
    end
  end

  [global_errors, output]
end

def get_conversions(directory)
  conversions = []
  ocaml_file_names = Dir.glob(File.join(directory, "**/*.ml{,i}")).to_a.sort
  ocaml_file_names.each_with_index do |ocaml_file_name, index|
    print "\r#{directory} (#{index + 1}/#{ocaml_file_names.size})"
    ocaml_name = Pathname.new(ocaml_file_name).relative_path_from(Pathname.new(directory)).to_s
    ocaml_content = File.read(ocaml_file_name, :encoding => 'utf-8')
    coq_file_name = ocaml_file_name + ".v"
    coq_name = File.basename(coq_file_name)
    errors_file_name = ocaml_file_name + ".errors"
    if File.exists?(coq_file_name) then
      errors_content = File.read(errors_file_name)
      errors_json = errors_content != "" ? JSON.parse(errors_content) : []
      global_errors, marked_ocaml_content = mark_text(ocaml_content, errors_json)
      coq_content = File.read(coq_file_name, :encoding => 'utf-8')
      if coq_content.valid_encoding? then
        conversions << [
          ocaml_name,
          errors_json.size,
          global_errors,
          marked_ocaml_content,
          coq_name,
          coq_content
        ]
      end
    end
  end
  puts
  conversions.sort_by {|ocaml_name, _, _, _| ocaml_name}
end

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
  project_name = :kernel
  project_intro = <<END
    <h2>Kernel of Coq</h2>
    <p>This is a demo of the current development version of <a href="https://github.com/clarus/coq-of-ocaml">coq-of-ocaml</a> on the <a href="https://github.com/coq/coq/tree/master/kernel">kernel</a> of <a =href="https://coq.inria.fr/">Coq</a>. Coq is written in <a =href="https://ocaml.org/">OCaml</a>. We show the original source code on the left and the imported Coq code on the right. The imported code probably does not compile. This is due to either various incompleteness in our tool, or to side-effects in the source code. Write at <code>web [at] clarus [dot] me</code> for more information. Work currently made at <a href="https://www.nomadic-labs.com/">Nomadic Labs</a>.</p>
END
  conversions = get_conversions(kernel_directory)
  file << ERB.new(File.read("template/project.html.erb")).result(binding)
end

File.open("tezos/index.html", "w") do |file|
  project_name = :tezos
  project_intro = <<END
    <h2>Tezos</h2>
    <p>These are the sources <a href="https://tezos.com/">Tezos</a> imported to <a href="https://coq.inria.fr/">Coq</a> by the current development version of <a href="https://github.com/clarus/coq-of-ocaml">coq-of-ocaml</a>. Tezos is a crypto-currency with smart-contracts and an upgradable protocol. The market cap of Tezos is more than US $500 millions at the time of writting. Write at <code>web [at] clarus [dot] me</code> for more information. Work currently made at <a href="https://www.nomadic-labs.com/">Nomadic Labs</a>.</p>
END
  conversions = get_conversions(tezos_directory)
  file << ERB.new(File.read("template/project.html.erb")).result(binding)
end
