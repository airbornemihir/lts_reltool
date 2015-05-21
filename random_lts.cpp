#include <iostream>
#include <vector>
typedef std::vector<unsigned int> VU;
typedef std::vector<VU> VVU;
#include <random>
#include <chrono>
#include <unistd.h>

std::default_random_engine generator(std::chrono::system_clock::now().time_since_epoch().count());

void fill(VVU &lts, unsigned int root, unsigned int size, VU &leaves) {
  if (size <= 1)
    leaves.push_back(root);
  else {
    // std::uniform_int_distribution<unsigned int> distribution(0,size - 1);
    // unsigned int left_subtree_size(distribution(generator));
    unsigned int left_subtree_size((size - 1) / 2);
    if (left_subtree_size > 0) {
      fill(lts, root + 1, left_subtree_size, leaves);
      lts[root - 1].push_back(root + 1);
    }
    if (left_subtree_size < size - 1) {
      fill(lts, root + 1 + left_subtree_size, size - 1 - left_subtree_size, leaves);
      lts[root - 1].push_back(root + 1 + left_subtree_size);
    }
  }
}

int main(int argc, char *argv[]) {
  bool cflag(false);
  unsigned int n; bool nflag(false);
  unsigned int buffer(0);
  for (int c;(c = getopt (argc, argv, "cb:n:")) != -1;)
    switch (c)
      {
      case 'c':
        cflag = true;
        break;
      case 'n':
        nflag = true;
        n = atoi(optarg);
        break;
      case 'b':
        buffer = atoi(optarg);
        break;
      case '?':
        if (optopt == 'n')
          {fprintf (stderr, "Option -%c requires an argument.\n", optopt); return 1;}
        else if (isprint (optopt))
          fprintf (stderr, "Unknown option `-%c'.\n", optopt);
        else
          fprintf (stderr,
                   "Unknown option character `\\x%x'.\n",
                   optopt);
        break;
      default:
        abort ();
      }
  if (!nflag)
    {fprintf (stderr, "Option -n is required.\n"); return 1;}
  VVU lts(n);
  VU leaves;
  fill(lts, 1, n, leaves);
  std::cout << "digraph {" << std::endl;
  if (cflag) {
    std::uniform_int_distribution<unsigned int> distribution(1,leaves.size());
    lts[leaves[distribution(generator) - 1] - 1].push_back(1);
  }
  for (unsigned int i1(1); i1 <= n; ++i1) 
    for (unsigned int i2(1); i2 <= lts[i1 - 1].size(); ++i2) 
      std::cout << (buffer + i1) << " -> " << (buffer + lts[i1 - 1][i2 - 1]) << " [\"label\" = 0]" << std::endl;
  std::cout << "}" << std::endl;
  return 0;
}
