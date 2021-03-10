// example06-complement_minimized - complementing an automaton

#include <fstream>
#include <iostream>
#include <vata2/nfa.hh>

using namespace Vata2::Nfa;

int main(int argc, char *argv[])
{
    if (argc != 2) {
        std::cerr << "Input file missing\n";
        return EXIT_FAILURE;
    }

    std::string filename = argv[1];

    std::fstream fs(filename, std::ios::in);
    if (!fs) {
        std::cerr << "Could not open file \'" << filename << "'\n";
        return EXIT_FAILURE;
    }

    Vata2::Parser::Parsed parsed;
    Nfa aut;
    StringToSymbolMap stsm;
    OnTheFlyAlphabet alph(&stsm);
    try {
        parsed = Vata2::Parser::parse_vtf(fs, true);
        fs.close();

        if (parsed.size() != 1) {
            throw std::runtime_error(
                "The number of sections in the input file is not 1\n");
        }
        if (parsed[0].type != "NFA") {
            throw std::runtime_error(
                "The type of input automaton is not NFA\n");
        }

        aut = construct(parsed[0], &alph);
    }
    catch (const std::exception &ex) {
        fs.close();
        std::cerr << "libVATA2 error: " << ex.what() << "\n";
        return EXIT_FAILURE;
    }

    Nfa cmpl = complement(aut, alph);
    Nfa minimized = minimize(cmpl);

    // std::cout << std::to_string(minimized);
    std::cout << "states: " << minimized << std::endl;
    return EXIT_SUCCESS;
}
