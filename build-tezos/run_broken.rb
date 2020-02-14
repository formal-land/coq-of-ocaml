# Try to compile broken Coq files to see their errors.

config = File.read("_CoqProject")
commented_lines = config.split("\n").select {|line| line.include?("#")}
broken_file_names = commented_lines.map {|line| line[1..-1]}

puts "#{broken_file_names.size} broken files"
for broken_file_name in broken_file_names do
  command = "coqc -R . Tezos -impredicative-set -type-in-type #{broken_file_name}"
  puts command
  system(command)
end
