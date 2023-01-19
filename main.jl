
# Implements DLX but uses bitsets for rows and has basic DP in the form of an order-2 cache
# Frontend is specifically for anagrammen and pangramming (anagramming on the alphabet).
using DataStructures
using Serialization
using ArgParse
using Combinatorics

#ABC = collect("əɑaɛeɪiɔoʏyøuœmnŋpbtdkfvszxhʋjrlɒʊʃʒ")
ABC = collect("abcdefghijklmnopqrstuvwxyz")

ABC_INDEX = Dict([ABC[i] => i-1 for i in eachindex(ABC)])
INDEX_ABC = Dict([i-1 => ABC[i] for i in eachindex(ABC)])
N = length(ABC)

function anagram_to_bitset(word_or_anagram::String)::UInt64
	return reduce(|, [1<<ABC_INDEX["$k$i"] for (k,v) in counter(word_or_anagram) for i in 1:v])	
end

function is_subword(a::String, b::String)
	ac = counter(a)
	return all(ac[k] >= v for (k,v) in counter(b))
end

# use with anagram a-z for isograms
function load_words(filename::String, anagram::String = "")::Vector{String}
	f = if length(anagram) == 0 (x -> true) else (x -> is_subword(anagram, x)) end
	return filter(f, readlines(filename)) |> unique
end

# this is unbearably slow for large bitsets
function build_cache(bitsets::Vector{UInt64})
	# we kunnen BitSet ook gebruiken, die heeft constant geheugen gebruik van ~8GB
	# wellicht de moeite waard voor het gigantische woordenboek?
	out = Set{UInt64}()
	#       776 962 unigrams
	# 1 815 991 895 bigrams

	# set creating performance starts to degrade at about 60k
	# but it's still more memory efficient up till about 500k
	# 2^36/8/1024^3 = 8GB
	# for normal alphabet memory use is trivial
	# 2^26/8/1024^2 = 8MB
	# conversely for 40chars you'd need 256GB of RAM
	# 2sqrt(8GB/sizeof(UInt64)) = 64k (lower bound)
	if length(bitsets) > 500_000
		out = BitSet()
	end

	for i in eachindex(bitsets)
		#if i % 10000 == 0
		#	println(i, "/", length(bitsets))
		#end
		rest = bitsets[i+1:end]
		union!(out, rest[(rest .& bitsets[i]) .== 0] .| bitsets[i])
	end
	return [Set{UInt64}(bitsets), out]
end

# define definite order of anagram representations
# this also implicitely defines the search heuristic (long words first)
function order(anagram::UInt64)
	anagram = anagram & ((1<<N)-1)
	return -(2^N * count_ones(anagram) + anagram)
end

function solve_bitsets(N::UInt8, cache, callback, bitsets::Vector{UInt64}, max_depth = 4, known::UInt64 = 0, solution::Vector{UInt64} = [])
	if known == (1<<N)-1
		callback(solution)
		return
	end

	if max_depth <= 2
		miss = ((1<<N)-1) - known
		# er is een N=1 oplossing?
		if miss in cache[1]
			callback([solution;[miss]])
		end
		# er is een N=2 oplossing?
		if miss in cache[2]
			for x in bitsets
				if miss - x in cache[1]
					if order(miss - x) > order(x)
						callback([solution; [x, miss-x]])
					end
					return
				end
			end
		end
		return
	end


	for i in eachindex(bitsets)
		# we know from the ordering that all words in bitsets[i:end] can have at most as many chars as bitsets[i]
		# so we can stop if that would not allow for sufficient characters before we hit the max. wordcount 
		if count_ones(bitsets[i]) * max_depth < N-count_ones(known)
			return
		end

		choice = bitsets[i]

		rest = bitsets[i+1:end]
		subset = rest[(rest .& choice) .== 0]

		push!(solution, choice)
		solve_bitsets(N, cache, callback, subset, max_depth - 1, known|choice, solution)
		pop!(solution)
	end
end

function solver_partial(N::UInt8, cache, callback, bitsets::Vector{UInt64}, max_depth, given)
	anagram = anagram_to_bitset(given)
	# solve_bitsets(cache, callback, bitsets::Vector{UInt64}, max_depth = 4, known::UInt64 = 0, solution::Vector{UInt64} = [])
	solve_bitsets(N, cache, callback, bitsets[(bitsets .& anagram) .== 0], max_depth-1, anagram, [anagram])
end

function solve_bitsets_mt(N::UInt8, cache, callback, bitsets::Vector{UInt64}, max_depth)
	limit = findfirst(x -> (count_ones(x) * max_depth < N), bitsets)
	indices = collect(eachindex(bitsets[1:limit-1]))

	Threads.@threads for i in indices
		choice = bitsets[i]
		rest = bitsets[i+1:end]
		solve_bitsets(N, cache, callback, rest[(rest .& choice) .== 0], max_depth - 1, choice, [choice])
	end

end

lookup = DefaultDict(Vector{String})

function parse_options()
	s = ArgParseSettings()
	@add_arg_table s begin
		"--dict", "-d"
			help = "Use word in given file, one per line assumed"
			arg_type = String
			required = true
		"--length", "-l"
			help = "Only find solutions with no more than this amount of words."
			arg_type = Int
			required = true
		"--anagram", "-a"
			help = "Find anagrams for input, if not provided will search for pangrams by using the alphabet (all unique unicode symbols) used in dictionary."
			arg_type = String
			default = ""
		"--used", "-u"
			help = "Letters provided will be substracted from alphabet (and count as first word of solution)"
			arg_type = String
			default = ""
		"--minimum", "-m"
			help =  "Minimum word length for each word in solution"
			arg_type = Int
			default = 1
	end

	return parse_args(s)
end

function solve()
	global ABC
	global ABC_INDEX
	global INDEX_ABC
	global N

	parsed_args = parse_options()
	filename = parsed_args["dict"]
	words = filter(x -> length(x) >= parsed_args["minimum"], readlines(filename)) |> collect
	println("Loaded $(length(words)) from $filename, minimum length is ", parsed_args["minimum"])
	
	anagram = parsed_args["anagram"]

	if length(anagram) > 0
		println("Selecting words that can be contained within ", parsed_args["anagram"])
		words = filter(x -> is_subword(parsed_args["anagram"], x), words) |> collect
		ABC = ["$k$i" for (k,v) in counter(parsed_args["anagram"]) for i in 1:v]	
	else
		println("No input provided, filtering on isograms and anagramming on alphabet.")
		words = filter(x -> length(x) == length(Set(x)), words) |> collect
		ABC = ["$(x[1])1" for x in sort(counter([c for w in words for c in w]) |> collect, by=(x->(-x[2], x[1])))]
		anagram = join(x[1] for x in ABC)
	end

	ABC_INDEX = Dict([ABC[i] => i-1 for i in eachindex(ABC)])
	INDEX_ABC = Dict([i-1 => ABC[i] for i in eachindex(ABC)])
	N = length(ABC)

	word_id_bits = Int(ceil(log2(length(words))))

	if N+word_id_bits > 64
		println("ERROR: 64 bits too small, alphabet is $(N) bits and dictionary requires $(word_id_bits) (eg: log2($(length(words))) which is more than 64.")
		exit()
	end

	anagrams::Vector{UInt64} = []

	totals = counter(anagram)
	for (i, w) in enumerate(words)
		# there are possibly multiple ways to interpret a word to a bitset
		letter_options = []
		for (k,v) in counter(w)
			push!(letter_options, [reduce(|, [1<<ABC_INDEX["$k$i"] for i in 1+offset:v+offset]) for offset in 0:totals[k]-v])
		end

		for x in Iterators.product(letter_options...)
			a = reduce(|, x)
			push!(anagrams, a) # |((i-1)<<N)
			push!(lookup[a], w)
		end
	end

	anagrams = sort(anagrams, by=order)
	anagrams = unique(anagrams)

	#println(words)

	println("Loaded ", length(anagrams), " bitsets from ", length(words), " words")
	println("Alphabet is ", join(ABC, " "))

	print_lock = ReentrantLock();
	function print_solution(solution)
		lock(print_lock) do
			println(join([join(lookup[x], ",") for x in solution], " "))
		end
	end


	if false && isfile(filename * ".cache")
		println("Found cache for file `" * filename * "`")
		cache = deserialize(filename * ".cache")
	else
		println("Building bigram cache for file `" * filename * "`")
		cache = build_cache(anagrams)
		serialize(filename * ".cache", cache)
	end
	println("Bigrammic cache contains ", length(cache[2]), " bitsets")

	#println("finding exact cover")
	# 4 =   18.23s
	# 5 =  110.88s
	# 6 = est: 18h (>10x DLX even on single core)

	# voor de grote dataset vinden we alle 4-oplossingen,
	# totaal 4:24:03.15
	#solve_bitsets(cache, print_solution, anagrams, UInt64(6), UInt64(0), Vector{UInt64}())
	#solve_bitsets_mt(cache, print_solution, anagrams, UInt64(5))

	if length(parsed_args["used"]) > 0
		solver_partial(UInt8(N), cache, print_solution, anagrams, parsed_args["length"], parsed_args["used"])
	else
		solve_bitsets(UInt8(N), cache, print_solution, anagrams, parsed_args["length"], UInt64(0), Vector{UInt64}())
	end
end

solve()

