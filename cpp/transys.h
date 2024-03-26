#pragma once

#include <vector>

extern "C" {
void *transys_from_aig(const char *);

void transys_drop(void *);

int transys_cube_subsume_init(void *, uint *, uint);
}

class Transys {
    public:
	Transys(const char *aig)
	{
		ptr = transys_from_aig(aig);
	}

	~Transys()
	{
		transys_drop(ptr);
	}

	bool cube_subsume_init(std::vector<uint> &cube)
	{
		return transys_cube_subsume_init(ptr, cube.data(), cube.size()) == 1;
	}

	void *ptr;
};
