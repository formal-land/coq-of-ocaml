# encoding: utf-8
# Run the tests in 'tests/'
require 'fileutils'

class Test
  attr_reader :source_file

  def initialize(source_file)
    @source_file = source_file
  end

  def extension(ext)
    File.join(File.dirname(@source_file), File.basename(@source_file, '.ml') + ext)
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

  def check(mode)
    coq_of_ocaml(mode) == reference(mode)
  end

  def coq_cmd
    "coqc #{extension('.v')}"
  end

  def coq
    system("#{coq_cmd} 2>/dev/null")
    $?.exitstatus == 0
  end
end

class Tests
  def initialize(source_files)
    @tests = source_files.sort.map {|source_file| Test.new(source_file) }
  end

  def compile
    puts "\e[1mCompiling:\e[0m"
    for test in @tests do
      test.compile
      puts
    end
  end

  def check(mode)
    puts "\e[1mChecking '-#{mode}':\e[0m"
    for test in @tests do
      if test.check(mode)
        print " \e[1;32m✓\e[0m "
      else
        print " \e[31m✗\e[0m "
      end
      puts test.coq_of_ocaml_cmd(mode).join(" ")
    end
  end

  def coq
    puts "\e[1mRunning coqc (compiles the reference files):\e[0m"
    for test in @tests do
      if test.coq
        print " \e[1;32m✓\e[0m "
      else
        print " \e[31m✗\e[0m "
      end
      puts test.coq_cmd
    end
  end
end

tests = Tests.new(Dir.glob('tests/ex*.ml'))
tests.compile
puts
tests.check('exp')
puts
tests.check('effects')
exit(0)
puts
tests.check('monadise')
puts
tests.check('v')
puts
tests.coq
