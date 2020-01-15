require 'open3'

tezos_folder = "../../../Tezos/gitlab/tezos"
protocol_folder = "#{tezos_folder}/src/proto_alpha/lib_protocol"
interface_file = "#{tezos_folder}/generated/Environment_mli.v"
environment_file = "Environment.v"

system("cp #{interface_file} #{environment_file}")
system("cp #{protocol_folder}/*.v ./")

files = [
  environment_file,
  "Raw_level_repr.v"
]

nb_valid_lines = 0

for file in files do
  command = "coqc -R . Tezos #{file}"
  puts command
  output, status = Open3.capture2e(command)
  if status.to_i == 0 then
    nb_lines = File.read(file).split("\n").size
    puts nb_lines
    nb_valid_lines += nb_lines if file != environment_file
  else
    puts output
    line_number = /line (\d+)/.match(output)[1]
    nb_valid_lines += line_number.to_i - 1 if file != environment_file
  end
end

puts "Total number of valid lines: #{nb_valid_lines}"
