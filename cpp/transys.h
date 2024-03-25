#pragma once

extern "C" {
void *transys_from_aig(const char *);

void drop_transys(void *);
}

class Transys {
    public:
	Transys(const char *aig)
	{
		ptr = transys_from_aig(aig);
	}

	~Transys()
	{
		drop_transys(ptr);
	}

    private:
	void *ptr;
};
