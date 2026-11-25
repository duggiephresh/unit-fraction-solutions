v = readvec("odd-znam/odd_znam_solution.txt");
k = #v; N = prod(i=1,k,v[i]);
ok = 1;
for(i=1,k, x=v[i]; o=N/x; if(x%2!=1 || x<=1 || (o+1)%x!=0 || x==o+1, ok=0; print("FAIL at ",i)));
for(i=1,k, for(j=i+1,k, if(gcd(v[i],v[j])!=1, ok=0; print("not coprime ",i," ",j))));
s = sum(i=1,k,1/v[i]) + 1/N;
print("k = ",k,"  all checks: ",ok,"  sum 1/x_i + 1/prod = ",s);
quit
