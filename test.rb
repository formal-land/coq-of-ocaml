# Run the tests in 'tests/'

class Test
  attr_reader :source_file

  def initialize(source_file)
    @source_file = source_file
  end

  def extension(ext)
    File.join(File.dirname(@source_file), File.basename(@source_file, '.ml') + ext)
  end

  def coq_of_ocaml(mode)
    system('ocamlc', '-bin-annot', @source_file)
    IO.popen(['./coqOfOCaml.native', '-mode', mode, extension('.cmt')]).read
  end

  def reference(mode)
    File.read(extension('.' + mode))
  end

  def check(mode)
    coq_of_ocaml(mode) == reference(mode)
  end
end

class Tests
  def initialize(source_files)
    @tests = source_files.map {|source_file| Test.new(source_file) }
  end

  def check(mode)
    puts "Checking '-#{mode}':"
    for test in @tests do
      print "  ./coqOfOCaml.native -mode #{mode} #{test.extension('.cmt')}\t"
      if test.check(mode)
        puts "\e[1;34m[ \e[32mOK \e[34m]\e[0m"
      else
        puts "\e[1;34m[ \e[31merror \e[34m]\e[0m"
      end
    end
  end
end

tests = Tests.new(Dir.glob('tests/ex*.ml'))
tests.check('exp')