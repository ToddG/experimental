# Tutorial

### Link: https://auth0.com/blog/kubernetes-tutorial-step-by-step-introduction-to-basic-concepts/

## Create
    
    # ignore, this is for my scripts
    $ set -x

### Start

Look at your baseline, what nodes|pods|namespaces|services are currently running?

    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services
    $ kubectl get replicationcontrollers
    $ kubectl get roles
    $ kubectl get secrets
    $ kubectl get endpoints

### Create deployment

A deployment.yaml specifies the containers : [{name,image,port}]. After running we should see pods (containers) created.

    $ kubectl apply -f deployment.yaml
    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services

### Download and apply ingress controller 1/2

Metric-ton of configuration for Nginx...

Note, I already downloaded and added this file to the repo.

    curl https://raw.githubusercontent.com/kubernetes/ingress-nginx/master/deploy/mandatory.yaml -o mandatory.yaml

On with the show...

    $ kubectl apply -f mandatory.yaml
    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services
    $ kubectl get pods -n ingress-nginx
    $ kubectl get services -n ingress-nginx


### Download and apply ingress controller 2/2

Specifies a service? : [port,port,...]

Note, I already downloaded and added this file to the repo.

    curl https://raw.githubusercontent.com/kubernetes/ingress-nginx/master/deploy/provider/cloud-generic.yaml -o cloud-generic.yaml

On with the show...

    $ kubectl apply -f cloud-generic.yaml
    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services
    $ kubectl get pods -n ingress-nginx
    $ kubectl get services -n ingress-nginx

### Expose deployment port via ClusterIP service

Specifies a port redirect from 80 to 3000 for selector -> '...-deployment'

    $ kubectl apply -f service.yaml
    $ kubectl get nodes
    $ kubectl get pods
    $ kubectl get namespaces
    $ kubectl get services
    $ kubectl get pods -n ingress-nginx

### Define service ingress

    $ kubectl apply -f ingress.yaml
    $ firefox $(kubectl get svc -n ingress-nginx ingress-nginx -o=jsonpath='{.status.loadBalancer.ingress[0].ip}')


## Sample Run

Run the create.sh script...

    + kubectl get nodes
    NAME                  STATUS   ROLES    AGE   VERSION
    toddg-pool-001-fg17   Ready    <none>   40h   v1.14.1
    toddg-pool-001-fg1m   Ready    <none>   40h   v1.14.1
    + kubectl get pods
    No resources found.
    + kubectl get namespaces
    NAME              STATUS   AGE
    default           Active   40h
    kube-node-lease   Active   40h
    kube-public       Active   40h
    kube-system       Active   40h
    + kubectl get services
    NAME         TYPE        CLUSTER-IP   EXTERNAL-IP   PORT(S)   AGE
    kubernetes   ClusterIP   10.245.0.1   <none>        443/TCP   40h
    + kubectl get replicationcontrollers
    No resources found.
    + kubectl get roles
    No resources found.
    + kubectl get secrets
    NAME                  TYPE                                  DATA   AGE
    default-token-kh4nd   kubernetes.io/service-account-token   3      40h
    + kubectl get endpoints
    NAME         ENDPOINTS            AGE
    kubernetes   159.89.143.223:443   40h
    + kubectl apply -f deployment.yaml
    deployment.apps/kubernetes-tutorial-deployment created
    + kubectl get nodes
    NAME                  STATUS   ROLES    AGE   VERSION
    toddg-pool-001-fg17   Ready    <none>   40h   v1.14.1
    toddg-pool-001-fg1m   Ready    <none>   40h   v1.14.1
    + kubectl get pods
    NAME                                              READY   STATUS              RESTARTS   AGE
    kubernetes-tutorial-deployment-8666f766d5-fxqpd   0/1     ContainerCreating   0          1s
    kubernetes-tutorial-deployment-8666f766d5-zqqlg   0/1     ContainerCreating   0          1s
    + kubectl get namespaces
    NAME              STATUS   AGE
    default           Active   40h
    kube-node-lease   Active   40h
    kube-public       Active   40h
    kube-system       Active   40h
    + kubectl get services
    NAME         TYPE        CLUSTER-IP   EXTERNAL-IP   PORT(S)   AGE
    kubernetes   ClusterIP   10.245.0.1   <none>        443/TCP   40h
    + kubectl apply -f mandatory.yaml
    namespace/ingress-nginx created
    configmap/nginx-configuration created
    configmap/tcp-services created
    configmap/udp-services created
    serviceaccount/nginx-ingress-serviceaccount created
    clusterrole.rbac.authorization.k8s.io/nginx-ingress-clusterrole created
    role.rbac.authorization.k8s.io/nginx-ingress-role created
    rolebinding.rbac.authorization.k8s.io/nginx-ingress-role-nisa-binding created
    clusterrolebinding.rbac.authorization.k8s.io/nginx-ingress-clusterrole-nisa-binding created
    deployment.apps/nginx-ingress-controller created
    + kubectl get nodes
    NAME                  STATUS   ROLES    AGE   VERSION
    toddg-pool-001-fg17   Ready    <none>   40h   v1.14.1
    toddg-pool-001-fg1m   Ready    <none>   40h   v1.14.1
    + kubectl get pods
    NAME                                              READY   STATUS    RESTARTS   AGE
    kubernetes-tutorial-deployment-8666f766d5-fxqpd   1/1     Running   0          5s
    kubernetes-tutorial-deployment-8666f766d5-zqqlg   1/1     Running   0          5s
    + kubectl get namespaces
    NAME              STATUS   AGE
    default           Active   40h
    ingress-nginx     Active   3s
    kube-node-lease   Active   40h
    kube-public       Active   40h
    kube-system       Active   40h
    + kubectl get services
    NAME         TYPE        CLUSTER-IP   EXTERNAL-IP   PORT(S)   AGE
    kubernetes   ClusterIP   10.245.0.1   <none>        443/TCP   40h
    + kubectl get pods -n ingress-nginx
    NAME                                        READY   STATUS    RESTARTS   AGE
    nginx-ingress-controller-5694ccb578-cwxnp   0/1     Running   0          2s
    + kubectl get services -n ingress-nginx
    No resources found.
    + kubectl apply -f cloud-generic.yaml
    service/ingress-nginx created
    + kubectl get nodes
    NAME                  STATUS   ROLES    AGE   VERSION
    toddg-pool-001-fg17   Ready    <none>   40h   v1.14.1
    toddg-pool-001-fg1m   Ready    <none>   40h   v1.14.1
    + kubectl get pods
    NAME                                              READY   STATUS    RESTARTS   AGE
    kubernetes-tutorial-deployment-8666f766d5-fxqpd   1/1     Running   0          9s
    kubernetes-tutorial-deployment-8666f766d5-zqqlg   1/1     Running   0          9s
    + kubectl get namespaces
    NAME              STATUS   AGE
    default           Active   40h
    ingress-nginx     Active   6s
    kube-node-lease   Active   40h
    kube-public       Active   40h
    kube-system       Active   40h
    + kubectl get services
    NAME         TYPE        CLUSTER-IP   EXTERNAL-IP   PORT(S)   AGE
    kubernetes   ClusterIP   10.245.0.1   <none>        443/TCP   40h
    + kubectl get pods -n ingress-nginx
    NAME                                        READY   STATUS    RESTARTS   AGE
    nginx-ingress-controller-5694ccb578-cwxnp   0/1     Running   0          5s
    + kubectl get services -n ingress-nginx
    NAME            TYPE           CLUSTER-IP    EXTERNAL-IP   PORT(S)                      AGE
    ingress-nginx   LoadBalancer   10.245.7.22   <pending>     80:32716/TCP,443:31260/TCP   3s
    + kubectl apply -f service.yaml
    service/kubernetes-tutorial-cluster-ip created
    + kubectl get nodes
    NAME                  STATUS   ROLES    AGE   VERSION
    toddg-pool-001-fg17   Ready    <none>   40h   v1.14.1
    toddg-pool-001-fg1m   Ready    <none>   40h   v1.14.1
    + kubectl get pods
    NAME                                              READY   STATUS    RESTARTS   AGE
    kubernetes-tutorial-deployment-8666f766d5-fxqpd   1/1     Running   0          13s
    kubernetes-tutorial-deployment-8666f766d5-zqqlg   1/1     Running   0          13s
    + kubectl get namespaces
    NAME              STATUS   AGE
    default           Active   40h
    ingress-nginx     Active   10s
    kube-node-lease   Active   40h
    kube-public       Active   40h
    kube-system       Active   40h
    + kubectl get services
    NAME                             TYPE        CLUSTER-IP      EXTERNAL-IP   PORT(S)   AGE
    kubernetes                       ClusterIP   10.245.0.1      <none>        443/TCP   40h
    kubernetes-tutorial-cluster-ip   ClusterIP   10.245.50.108   <none>        80/TCP    1s
    + kubectl get pods -n ingress-nginx
    NAME                                        READY   STATUS    RESTARTS   AGE
    nginx-ingress-controller-5694ccb578-cwxnp   0/1     Running   0          9s
    + kubectl apply -f ingress.yaml
    ingress.extensions/kubernetes-tutorial-ingress created
    ++ kubectl get svc -n ingress-nginx ingress-nginx '-o=jsonpath={.status.loadBalancer.ingress[0].ip}'
    + firefox 138.197.239.23


## Destroy

You can destroy all these resources by running the `teardown.sh` script.
