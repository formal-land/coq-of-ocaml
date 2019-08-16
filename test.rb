# encoding: utf-8
# Run the tests in 'tests/'
require 'fileutils'

class Test
  attr_reader :source_file

  def initialize(source_file)
    @source_file = source_file
  end

  def base_name
    File.basename(@source_file, '.ml')
  end

  def extension(ext)
    File.join(File.dirname(@source_file), base_name + ext)
  end

  def compile
    cmd = ['ocamlc', '-bin-annot', @source_file]
    print cmd.join(" ")
    system(*cmd)
  end

  def coq_of_ocaml_cmd(mode)
    cmd = ['./coqOfOCaml.native', '-mode', mode, extension('.cmt')]
  end

  def coq_of_ocaml(mode)
    IO.popen(coq_of_ocaml_cmd(mode)).read
  end

  def reference(mode)
    file_name = extension('.' + mode)
    FileUtils.touch file_name unless File.exists?(file_name)
    File.read(file_name)
  end

  # Update the reference snapshot file.
  def update(mode)
    output = coq_of_ocaml(mode)
    file_name = extension('.' + mode)
    File.write(file_name, output)
  end

  def check(mode)
    coq_of_ocaml(mode) == reference(mode)
  end

  def coq_cmd
    "coqc #{extension('.v')} -R tests Tests"
  end

  def coq
    system("#{coq_cmd} 2>/dev/null")
    return $?.exitstatus == 0
  end

  def extraction_cmd
    disable_fatal_warnings = "-lflags '-warn-error -a'"
    "cd tests/extraction && coqc extract.v -R .. Tests -R ../../OCaml OCaml && ocamlbuild #{disable_fatal_warnings} #{base_name}.byte && ./#{base_name}.byte"
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

  def compile
    puts "\e[1mCompiling:\e[0m"
    for test in @tests do
      test.compile
      puts
    end
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

  def check(mode)
    puts "\e[1mChecking '-#{mode}':\e[0m"
    for test in @tests do
      print_result(test.check(mode))
      puts test.coq_of_ocaml_cmd(mode).join(" ")
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
      print_result(test.extraction)
      puts test.extraction_cmd
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

black_list = [
  "ex09",
  "ex20",
  "ex25",
  "ex27",
  "ex33"
]

test_files = Dir.glob('tests/ex*.ml').select do |file_name|
  not black_list.any? {|black_listed_test| "tests/#{black_listed_test}.ml" == file_name}
end
tests = Tests.new(test_files)
tests.compile
puts
tests.check('exp')
puts
tests.check('v')
puts
tests.coq
puts
tests.extraction
tests.print_summary

exit(1) if tests.invalid?
