 void real2()
 {
   int tab[10];
   int len;
   int   tmp;
   int   again;
   int   i;
 
   for (again = 1; again;)
     for (again = 0, i = 0; i < (len - 1); i++)
       {
         if (tab[i] > tab[i + 1])
           {
             tmp = tab[i];
             tab[i] = tab[i + 1];
             tab[i + 1] = tmp;
             again = 1;
           }
       }
 }
