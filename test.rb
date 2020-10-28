# encoding: utf-8
# Run the tests in 'tests/'
require 'fileutils'

def patch_with_monadic_notations(content)
  pattern = "Definition insert_monadic_notations_here : unit := tt.\n"
  replacement = <<-END
Notation "'let*' x ':=' X 'in' Y" :=
  (op_letstar X (fun x => Y))
  (at level 200, x ident, X at level 100, Y at level 200).

Notation "'let*' ' x ':=' X 'in' Y" :=
  (op_letstar X (fun x => Y))
  (at level 200, x pattern, X at level 100, Y at level 200).
  END

  content.gsub(pattern, replacement)
end

class Test
  attr_reader :source_file

  def initialize(source_file)
    @source_file = source_file
  end

  def base_name
    File.basename(@source_file, '.*')
  end

  def generated_name
    File.join(File.dirname(@source_file), base_name + '.v')
  end

  def coq_of_ocaml_cmd
    coq_of_ocaml = '_build/default/src/coqOfOCaml.exe'
    cmd = [coq_of_ocaml, '-output', '/dev/stdout', @source_file]
  end

  def coq_of_ocaml
    # We remove the fist line which is a success message
    output = IO.popen(coq_of_ocaml_cmd, :external_encoding => "utf-8").read.split("\n")[1..-1].join("\n") + "\n"
    if base_name == "monadic_notation" then
      patch_with_monadic_notations(output)
    else
      output
    end
  end

  def reference
    file_name = generated_name
    FileUtils.touch file_name unless File.exists?(file_name)
    File.read(file_name, :encoding => 'utf-8')
  end

  # Update the reference snapshot file.
  def update
    output = coq_of_ocaml
    file_name = generated_name
    File.write(file_name, output)
  end

  def check
    coq_of_ocaml == reference
  end

  def coq_cmd
    "coqc #{generated_name} -R tests Tests -R OCaml OCaml -impredicative-set"
  end

  def coq
    system("#{coq_cmd} 2>/dev/null")
    return $?.exitstatus == 0
  end

  def extraction_cmd
    disable_fatal_warnings = "-lflags '-warn-error -a'"
    "cd tests/extraction && coqc extract.v -R .. Tests -R ../../OCaml OCaml -impredicative-set && ocamlbuild #{disable_fatal_warnings} #{base_name}.byte && ./#{base_name}.byte"
  end

  def extraction
    FileUtils.rm_rf(["tests/extraction"])
    FileUtils.mkdir_p("tests/extraction")
    File.open("tests/extraction/extract.v", "w") do |f|
      f << <<-EOF
Require Import Tests.#{base_name}.

Recursive Extraction Library #{base_name}.
      EOF
    end
    system("(#{extraction_cmd}) >/dev/null")
    return $?.exitstatus == 0
  end
end

class Tests
  def initialize(source_files)
    @tests = source_files.sort.map {|source_file| Test.new(source_file) }
    @valid_tests = 0
    @invalid_tests = 0
  end

  def print_result(result)
    if result
      @valid_tests += 1
      print " \e[1;32m✓\e[0m "
    else
      @invalid_tests += 1
      print " \e[31m✗\e[0m "
    end
  end

  def check
    puts "\e[1mChecking '.v':\e[0m"
    for test in @tests do
      print_result(test.check)
      puts test.coq_of_ocaml_cmd.join(" ")
    end
  end

  def coq
    puts "\e[1mRunning coqc (compiles the reference files):\e[0m"
    for test in @tests do
      print_result(test.coq)
      puts test.coq_cmd
    end
  end

  def extraction
    puts "\e[1mCompiling and running the extracted programs:\e[0m"
    for test in @tests do
      if File.extname(test.source_file) != ".mli" then
        print_result(test.extraction)
        puts test.extraction_cmd
      end
    end
  end

  def print_summary
    puts
    puts "Total: #{@valid_tests} / #{@valid_tests + @invalid_tests}."
  end

  def invalid?
    @invalid_tests != 0
  end
end

test_files = Dir.glob('tests/*.ml*').select do |file_name|
  not file_name.include?("disabled")
end
tests = Tests.new(test_files)
tests.check
puts
tests.coq
# We do not test the extraction for now as it fails due to axioms. We will see
# how to deal with it latter.
# tests.extraction
tests.print_summary

exit(1) if tests.invalid?
