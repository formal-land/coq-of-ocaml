# encoding: UTF-8
require 'erb'
require 'json'
require 'pathname'
include(ERB::Util)

# Command line arguments.
kernel_directory, tezos_directory, tezos_interface_directory = ARGV

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
  ocaml_file_names = Dir.glob(File.join(directory, "**/*.ml{,i}")).to_a.sort.select {|file_name|
    not file_name.include?("test")
  }
  ocaml_file_names.each_with_index do |ocaml_file_name, index|
    print "\r#{directory} (#{index + 1}/#{ocaml_file_names.size})"
    ocaml_name = Pathname.new(ocaml_file_name).relative_path_from(Pathname.new(directory)).to_s
    ocaml_content = File.read(ocaml_file_name, :encoding => 'utf-8')
    coq_extension = File.extname(ocaml_file_name) == ".ml" ? ".v" : "_mli.v"
    ocaml_base_name = File.basename(ocaml_file_name, ".*")
    capitalized_base_name = ocaml_base_name[0].capitalize + ocaml_base_name[1..-1]
    coq_file_name = File.join(
      File.dirname(ocaml_file_name),
      capitalized_base_name + coq_extension
    )
    coq_name = File.basename(coq_file_name)
    errors_file_name = ocaml_file_name + ".errors"
    if File.exists?(coq_file_name) then
      errors_content = File.read(errors_file_name)
      errors_json = errors_content != "" ? JSON.parse(errors_content) : []
      global_errors, marked_ocaml_content = mark_text(ocaml_content, errors_json)
      nb_errors = errors_json.size - global_errors.size
      coq_content = File.read(coq_file_name, :encoding => 'utf-8')
      if coq_content.valid_encoding? then
        conversions << {
          ocaml_name: ocaml_name,
          nb_errors: nb_errors,
          global_errors: [],
          ocaml_content: marked_ocaml_content,
          ocaml_size: ocaml_content.split("\n").size,
          raw_ocaml_content: ocaml_content,
          coq_name: coq_name,
          coq_content: coq_content,
          coq_size: coq_content.split("\n").size
        }
      end
    else
      puts
      puts "'#{coq_file_name}' not found"
    end
  end
  puts
  conversions.sort_by {|conversion| conversion[:ocaml_name]}
end

# Helpers.
def header(root, section)
  ERB.new(File.read("template/header.html.erb")).result(binding)
end

def footer(root)
  ERB.new(File.read("template/footer.html.erb")).result(binding)
end

def project(name, title, intro, block_quote, directory, status, chart_data)
  project_name = name
  project_intro = <<-END
    <h2>
      #{title} in&nbsp;Coq
      <small>
      #{
        case status
        when :does_compile
          "<span class=\"label label-success\">Does compile</span>"
        when :active_development
          "<span class=\"label label-warning\">Active development</span>"
        when :does_not_compile
          "<span class=\"label label-danger\">Does not compile</span>"
        end
      }
      </small>
    </h2>
    <p>#{intro}</p>
    #{"<blockquote class=\"blockquote\"><p class=\"mb-0\" style=\"font-size: 16px;\">#{block_quote}</p></blockquote>" if block_quote}
  END
  conversions = get_conversions(directory)
  nb_ocaml_lines = conversions.reduce(0) {|sum, conversion|
    sum + conversion[:ocaml_size]
  }
  nb_coq_lines = conversions.reduce(0) {|sum, conversion|
    sum + conversion[:coq_size]
  }
  nb_errors = conversions.reduce(0) {|sum, conversion|
    sum + conversion[:nb_errors]
  }
  ERB.new(File.read("template/project.html.erb")).result(binding)
end

# Generate the files.
File.open("index.html", "w") do |file|
  file << ERB.new(File.read("index.html.erb")).result(binding)
end

File.open("kernel/index.html", "w") do |file|
  file << project(
    :kernel,
    "Kernel of Coq",
    "This is a demo of the current development version of <a href=\"https://github.com/clarus/coq-of-ocaml\">coq-of-ocaml</a> on the <a href=\"https://github.com/coq/coq/tree/master/kernel\">kernel</a> of <a =href=\"https://coq.inria.fr/\">Coq</a>. Coq is written in <a =href=\"https://ocaml.org/\">OCaml</a>.",
    nil,
    kernel_directory,
    :does_not_compile,
    nil
  )
end

File.open("tezos/index.html", "w") do |file|
  file << project(
    :tezos,
    "Protocol of Tezos",
    "These are the sources of the <a href=\"https://gitlab.com/tezos/tezos/tree/master/src/proto_alpha/lib_protocol\">protocol</a> of <a href=\"https://tezos.com/\">Tezos</a> imported to <a href=\"https://coq.inria.fr/\">Coq</a> by the current development version of <a href=\"https://github.com/clarus/coq-of-ocaml\">coq-of-ocaml</a>. Tezos is a crypto-currency with smart-contracts and an upgradable protocol.",
    "(2020-01-25) The import of Tezos code to Coq is currently on pause to consolitate gains (work on small features, write documentation). Our next targets will probably be the files with a lot of GADTs and the functors of the storage.",
    tezos_directory,
    :active_development,
    <<-END
      {
        compiling: [
          13,
          292,
          1784,
          1529,
          1147,
          1541,
          2680,
          3100,
          2962,
          5892,
          9302,
          9302,
          9302,
          9302,
        ],
        generated: [
          47563,
          41904,
          43481,
          43404,
          44618,
          45107,
          44768,
          45158,
          46874,
          46800,
          49535,
          49535,
          49535,
          49535,
        ],
        labels: [
          "01-14",
          "01-15",
          "01-16",
          "01-17",
          "01-18",
          "01-19",
          "01-20",
          "01-21",
          "01-22",
          "01-23",
          "01-24",
          "01-25",
          "01-26",
          "01-27",
        ]
      }
    END
  )
end

File.open("tezos-interface/index.html", "w") do |file|
  file << project(
    :tezos_interface,
    "Interface of the protocol of Tezos",
    "These are the sources of the interface of the <a href=\"https://gitlab.com/tezos/tezos/tree/master/src/proto_alpha/lib_protocol\">protocol</a> of <a href=\"https://tezos.com/\">Tezos</a> imported to <a href=\"https://coq.inria.fr/\">Coq</a> by the current development version of <a href=\"https://github.com/clarus/coq-of-ocaml\">coq-of-ocaml</a>. Tezos is a crypto-currency with smart-contracts and an upgradable protocol.",
    nil,
    tezos_interface_directory,
    :does_compile,
    <<-END
      {
        compiling: [
          7,
          826,
          1190,
          2184,
          6443,
        ],
        generated: [
          2185,
          2200,
          2829,
          6265,
          6443,
        ],
        labels: [
          "01-05",
          "01-06",
          "01-07",
          "01-08",
          "01-09",
        ]
      }
    END
  )
end
