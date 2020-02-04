require 'open3'

tezos_folder = "../../../Tezos/gitlab/tezos"
protocol_folder = "#{tezos_folder}/src/proto_alpha/lib_protocol"
interface_file = "#{tezos_folder}/generated/Environment_mli.v"
environment_file = "Environment.v"

system("rm *.glob *.v *.vo")
system("cp #{interface_file} #{environment_file}")
system("cp #{protocol_folder}/*.v ./")

files = [
  environment_file,
  "Blinded_public_key_hash.v",
  "Nonce_hash.v",
  "Period_repr.v",
  "Qty_repr.v",
  "Contract_hash.v",
  "Gas_limit_repr.v",
  "Cycle_repr.v",
  "Raw_level_repr.v",
  "Voting_period_repr.v",
  "Michelson_v1_primitives.v",
  "Storage_description.v",
  "Gas_limit_repr_mli.v",
  "Level_repr_mli.v",
  "Manager_repr_mli.v",
  "Manager_repr.v",
  "Michelson_v1_primitives_mli.v",
  "Misc_mli.v",
  "Misc.v",
  "Period_repr_mli.v",
  "Raw_level_repr_mli.v",
  "State_hash.v",
  "Script_expr_hash.v",
  "Script_int_repr_mli.v",
  "Script_int_repr.v",
  "Script_repr_mli.v",
  "Seed_repr_mli.v",
  "Storage_description_mli.v",
  "Tez_repr_mli.v",
  "Vote_repr_mli.v",
  "Vote_repr.v",
  "Voting_period_repr_mli.v",
  "Block_header_repr_mli.v",
  "Tez_repr.v",
  "Contract_repr.v",
  "Level_repr.v",
  "Script_repr.v",
  "Contract_repr_mli.v",
  "Cycle_repr_mli.v",
  "Legacy_script_support_repr_mli.v",
  "Legacy_script_support_repr.v",
  "Script_timestamp_repr_mli.v",
  "Commitment_repr.v",
  "Constants_repr.v",
  "Fitness_repr.v",
  "Parameters_repr.v",
  "Seed_repr.v",
  "Raw_context.v",
  "Roll_repr.v",
  "Constants_storage.v",
  "Level_storage.v",
  "Storage_sigs.v"
]

nb_valid_lines = 0

for file in files do
  command = "coqc -R . Tezos #{file} -impredicative-set"
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
