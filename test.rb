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

  def coq_of_ocaml(mode)
    cmd = ['./coqOfOCaml.native', '-mode', mode, extension('.cmt')]
    print cmd.join(" ")
    IO.popen(cmd).read
  end

  def reference(mode)
    file_name = extension('.' + mode)
    FileUtils.touch file_name unless File.exists?(file_name)
    File.read(file_name)
  end

  def check(mode)
    coq_of_ocaml(mode) == reference(mode)
  end

  def clean
    for ext in ['.cmt', '.cmi', '.cmo', '.glob', '.vo'] do
      FileUtils.rm_f(extension(ext))
    end
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
        puts "  \e[1;34m[ \e[32mOK \e[34m]\e[0m"
      else
        puts "  \e[1;34m[ \e[31merror \e[34m]\e[0m"
      end
    end
  end

  def clean
    puts "\e[1mCleaning.\e[0m"
    for test in @tests do
      test.clean
    end
  end
end

tests = Tests.new(Dir.glob('tests/ex*.ml'))
tests.compile
puts
tests.check('exp')
puts
tests.check('effects')
puts
tests.check('monadise')
puts
tests.clean